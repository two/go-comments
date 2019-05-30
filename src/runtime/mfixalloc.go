// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Fixed-size object allocator. Returned memory is not zeroed.
//
// See malloc.go for overview.

package runtime

import "unsafe"

// FixAlloc is a simple free-list allocator for fixed size objects.
// Malloc uses a FixAlloc wrapped around sysAlloc to manage its
// mcache and mspan objects.
//
// Memory returned by fixalloc.alloc is zeroed by default, but the
// caller may take responsibility for zeroing allocations by setting
// the zero flag to false. This is only safe if the memory never
// contains heap pointers.
//
// The caller is responsible for locking around FixAlloc calls.
// Callers can keep state in the object but the first word is
// smashed by freeing and reallocating.
//
// Consider marking fixalloc'd types go:notinheap.
// 是一个基于自由列表的固定大小的分配器。
// 其核心原理是将若干未分配的内存块连接起来，
// 将未分配的区域的第一个字为指向下一个未分配区域的指针使用
//
// fixalloc 是一个简单的固定大小对象的自由表内存分配器。
// Malloc 使用围绕 sysAlloc 的 fixalloc 来管理其 MCache 和 MSpan 对象。
//
// fixalloc.alloc 返回的内存默认为零，但调用者可以通过将 zero 标志设置为 false
// 来自行负责将分配归零。如果这部分内存永远不包含堆指针，则这样的操作是安全的。
//
// 调用方负责锁定 fixalloc 调用。调用方可以在对象中保持状态，
// 但当释放和重新分配时第一个字会被破坏。
//
// 考虑使 fixalloc 的类型变为 go:notinheap.
type fixalloc struct {
	size   uintptr
	first  func(arg, p unsafe.Pointer) // called first time p is returned 首次调用时返回 p
	arg    unsafe.Pointer
	list   *mlink
	chunk  uintptr // use uintptr instead of unsafe.Pointer to avoid write barriers
	nchunk uint32
	inuse  uintptr // in-use bytes now 正在使用的字节
	stat   *uint64
	zero   bool // zero allocations 归零的分配
}

// A generic linked list of blocks.  (Typically the block is bigger than sizeof(MLink).)
// Since assignments to mlink.next will result in a write barrier being performed
// this cannot be used by some of the internal GC structures. For example when
// the sweeper is placing an unmarked object on the free list it does not want the
// write barrier to be called since that could result in the object being reachable.
//
//go:notinheap
type mlink struct {
	next *mlink
}

// Initialize f to allocate objects of the given size,
// using the allocator to obtain chunks of memory.
// 初始化 f 来分配给定大小的对象。
// 使用分配器来按 chunk 获取
func (f *fixalloc) init(size uintptr, first func(arg, p unsafe.Pointer), arg unsafe.Pointer, stat *uint64) {
	f.size = size
	f.first = first
	f.arg = arg
	f.list = nil
	f.chunk = 0
	f.nchunk = 0
	f.inuse = 0
	f.stat = stat
	f.zero = true
}

// 内存分配
func (f *fixalloc) alloc() unsafe.Pointer {
	if f.size == 0 {
		print("runtime: use of FixAlloc_Alloc before FixAlloc_Init\n")
		throw("runtime: internal error")
	}
	// 存在被释放、可复用的内存
	// 也就是在运行时内存被释放，
	// 但这部分内存并不会被立即回收给操作系统，
	// 我们直接从自由表中获得即可，
	// 但需要注意按需将这部分内存进行清零操作
	if f.list != nil {
		// 取出 f.list
		v := unsafe.Pointer(f.list)
		// 并将其指向下一段区域
		f.list = f.list.next
		// 增加使用的(分配)大小
		f.inuse += f.size
		// 如果需要对内存清零，则对取出的内存执行初始化
		if f.zero {
			memclrNoHeapPointers(v, f.size)
		}
		// 返回分配的内存
		return v
	}

	// f.list 中没有可复用的内存

	// 如果此时 nchunk 不足以分配一个 size
	if uintptr(f.nchunk) < f.size {
		// 则向操作系统申请内存，大小为 16 << 10 pow(2,14)
		f.chunk = uintptr(persistentalloc(_FixAllocChunk, 0, f.stat))
		f.nchunk = _FixAllocChunk
	}
	// 指向申请好的内存
	v := unsafe.Pointer(f.chunk)
	if f.first != nil { // first 只有在 fixalloc 作为 spanalloc 时候，才会被设置为 recordspan
		f.first(f.arg, v) // 用于为 heap.allspans 添加新的 span
	}
	// 扣除并保留 size 大小的空间
	f.chunk = f.chunk + f.size
	f.nchunk -= uint32(f.size)
	f.inuse += f.size // 记录已经使用的大小
	return v
}

// 回收：直接将回收的地址指针放回到自由表中即可
func (f *fixalloc) free(p unsafe.Pointer) {
	// 减少使用的字节数
	f.inuse -= f.size
	// 将要释放的内存地址作为 mlink 指针插入到 f.list 内，完成回收
	v := (*mlink)(p)
	v.next = f.list
	f.list = v
}

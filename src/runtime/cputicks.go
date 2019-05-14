// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build !arm
// +build !arm64
// +build !mips64
// +build !mips64le
// +build !mips
// +build !mipsle
// +build !wasm

package runtime

// careful: cputicks is not guaranteed to be monotonic! In particular, we have
// noticed drift between cpus on certain os/arch combinations. See issue 8976.
// 具体实现平台相关，例如: ./src/runtime/asm_amd64.s:TEXT runtime·cputicks(SB),NOSPLIT,$0-0
func cputicks() int64

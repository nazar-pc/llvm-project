; RUN: llc -mtriple=riscv64 -mcpu=generic-rv64 < %s \
; RUN:   | FileCheck %s --check-prefix=RV64
; RUN: llc -mtriple=riscv64 -mcpu=generic-interpreter-rv64 < %s \
; RUN:   | FileCheck %s --check-prefix=INTERP
; RUN: llc -mtriple=riscv64 -mcpu=generic-rv64 -mattr=+interpreter-target < %s \
; RUN:   | FileCheck %s --check-prefix=INTERP

; A condition that is the conjunction of two comparisons becomes a chain of
; branches for hardware, whose predictor learns them. An interpreter turns each
; of those into a host indirect jump whose target depends on guest data and
; which the host predictor cannot learn, so the condition is computed instead
; and only one branch is left.

define i32 @and_of_loads(ptr %p, ptr %q) {
; RV64-LABEL: and_of_loads:
; RV64:         lw a0, 0(a0)
; RV64-NEXT:    blez a0, .LBB0_{{[0-9]+}}
; RV64:         lw a0, 0(a1)
; RV64:         blt {{a[0-9]+}}, {{a[0-9]+}}, .LBB0_{{[0-9]+}}
;
; INTERP-LABEL: and_of_loads:
; INTERP:         lw a0, 0(a0)
; INTERP-NEXT:    lw a1, 0(a1)
; INTERP-NEXT:    sgtz a0, a0
; INTERP-NEXT:    slti a1, a1, 42
; INTERP-NEXT:    and a0, a0, a1
; INTERP-NEXT:    beqz a0, .LBB0_{{[0-9]+}}
entry:
  %a = load i32, ptr %p
  %b = load i32, ptr %q
  %c1 = icmp sgt i32 %a, 0
  %c2 = icmp slt i32 %b, 42
  %cond = and i1 %c1, %c2
  br i1 %cond, label %then, label %else

then:
  ret i32 1

else:
  ret i32 2
}

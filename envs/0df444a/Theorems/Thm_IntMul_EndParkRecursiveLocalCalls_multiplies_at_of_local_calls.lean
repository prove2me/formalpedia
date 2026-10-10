-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveLocalCalls_multiplies_at_of_local_calls
-- name    : IntMul.EndParkRecursiveLocalCalls.multiplies_at_of_local_calls
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T08:26:48.855985+00:00
-- url     : https://prove2.me/theorems/548f95bf-f848-46c7-9838-a58801494c82
-- title:
--   Actual fixed-tape multiplication recurrence from local child count and work
-- statement:
--   Suppose the same fixed physical recursive scheduler multiplies all childWidth-bit operands within real time τ. Suppose its concrete finite local invocation certificates multiply all n-bit operands, with at most A calls on exactly childWidth-bit operands and native caller overhead at most B. Then this very same physical machine multiplies n-bit operands within A*τ+B. Each child is a complete finite evaluation of the actual machine. Its native halt clock is charged with coefficient one; local word work pays all physical reservation, restoration, input and output overhead. No oracle, trajectory assumption or child-budget cost remains. A and B may be real, so the result applies directly to coefficients such as 12T/r.
-- source:
--   Original actual-machine coefficient-one recurrence compiler for integer multiplication. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveLocalCalls
import Theorems.Thm_IntMul_EndParkRecursiveClockedCalls_native_clocked_calls_correct
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveLocalCalls IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveLocalCalls.multiplies_at_of_local_calls (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (n childWidth : ℕ) (A B τ : ℝ)
    (multiplies : MultipliesAt (machine M labels request resume) childWidth τ)
    (body : ∀ x y : List Bool, x.length=n → y.length=n →
      ∃ steps calls work,
        HasLocalCalls M labels request resume childWidth (initialExtent M x y) (M.initCfg x y)
          [] (bin (2*n) (val x*val y)) steps calls work ∧
        (calls : ℝ) ≤ A ∧
        (nativeOverhead M x y (bin (2*n) (val x*val y)) steps work : ℝ) ≤ B) :
    MultipliesAt (machine M labels request resume) n (A*τ+B) := by sorry

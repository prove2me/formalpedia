-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveClockedCalls_native_clocked_calls_correct
-- name    : IntMul.EndParkRecursiveClockedCalls.native_clocked_calls_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T08:07:11.727022+00:00
-- url     : https://prove2.me/theorems/7e11c1fb-04d1-46a9-9a33-238e33fb470b
-- title:
--   Complete native recursive runtime with coefficient-one actual child clocks
-- statement:
--   A finite local invocation certificate supplies actual native halt clocks for children of the same fixed recursive scheduler, finite correct child evaluations, local ordinary body steps and local word charges. The complete actual native machine reaches the exact whole final frame and canonical result in time at most the SUM of child halt clocks with coefficient ONE, plus local steps and a fixed linear bound on local word work, initial input, output and replenished head-distance potential. Retained bank extents and child logical budgets do not appear in the final runtime. No oracle, depth-dependent tape count or extra child-clock multiplier is used.
-- source:
--   Original coefficient-one actual native child-clock recurrence with amortized local word overhead. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveClockedCalls
import Theorems.Thm_IntMul_EndParkRecursiveReturn_return_cleanup_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveCall_call_entry_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveResume_resume_parent_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_to_interior_clock
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveClockedCalls IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveClockedCalls.native_clocked_calls_correct (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (x y w : List Bool) (steps clocks work : ℕ)
    (certificate : HasClockedCalls M labels request resume (initialExtent M x y)
      (M.initCfg x y) [] w steps clocks work) :
    ∃ t, t ≤ clocks+steps+32*(work+(M.k+1)*(inputWord M x y).length+M.k+(2*M.k+3)*steps)+
        5*(inputWord M x y).length+4*w.length+18 ∧
      (machine M labels request resume).step^[t] ((machine M labels request resume).initCfg x y)=
        nativeFinalFrame M labels request resume x y w ∧
      (machine M labels request resume).HaltsWithOutput x y t w := by sorry

-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_prefix_clock
-- name    : IntMul.EndParkRecursiveEvaluation.native_prefix_clock
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T04:36:16.920895+00:00
-- url     : https://prove2.me/theorems/d753a239-4976-4eeb-9486-62ccd80655f3
-- title:
--   Actual recursive body and cleanup prefix lies strictly before every native halt clock
-- statement:
--   For a finite evaluation of the fixed body on native input and any actual native halt clock H of the optimized recursive machine, there are actual bootstrap and complete body/cleanup times b and q with b ≤ 5|x#y|+12, q ≤ budget and b+q < H. Both reached configurations are given exactly: the initialized native body frame and the fully cleaned root stack-inspection frame. Thus the body/cleanup clock q is bounded by the actual native clock with coefficient one, even when the logical evaluation budget is conservative. This is a native prefix theorem; transfer of the same physical trace to an arbitrary interior child bank is separate.
-- source:
--   Original exact native-prefix clock domination theorem for recursive integer-multiplication foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_evaluates_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveEvaluation IntMul.EndParkRecursiveScheduler IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveEvaluation.native_prefix_clock (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (x y w : List Bool) (budget H : ℕ)
    (evaluation : Evaluates M labels request resume (initialExtent M x y)
      (M.initCfg x y) [] w budget)
    (halt : ((machine M labels request resume).step^[H]
      ((machine M labels request resume).initCfg x y)).state=
        (machine M labels request resume).qHalt) :
    ∃ b q : ℕ, b≤5*(inputWord M x y).length+12 ∧ q≤budget ∧ b+q<H ∧
      (machine M labels request resume).step^[b] ((machine M labels request resume).initCfg x y)=
        bodyFrame M labels request resume (nativeBase M labels request resume x y) 1 1
          (fun _ => 1) (initialExtent M x y) (M.initCfg x y) [] ∧
      (machine M labels request resume).step^[q]
        (bodyFrame M labels request resume (nativeBase M labels request resume x y) 1 1
          (fun _ => 1) (initialExtent M x y) (M.initCfg x y) [])=
        EndParkRecursiveReturn.inspectionFrame M labels request resume
          (nativeBase M labels request resume x y) 1 1 (fun _ => 1) w := by sorry

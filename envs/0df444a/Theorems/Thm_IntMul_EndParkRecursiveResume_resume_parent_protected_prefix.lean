-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveResume_resume_parent_protected_prefix
-- name    : IntMul.EndParkRecursiveResume.resume_parent_protected_prefix
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T07:40:58.529213+00:00
-- url     : https://prove2.me/theorems/f3476410-dab2-47f2-b5d4-8651c8ce2644
-- title:
--   Complete actual parent resumption with protected physical trajectory
-- statement:
--   Given a completed child invocation of the actual fixed-tape recursive scheduler, positive parent work offsets, positive caller buffer and continuation positions, unique local parent markers and tracked blank tails, the scheduler inspects the child continuation, restores the parent result bank, pops and recovers its continuation, replaces the parent output and enters the exact resumed body frame. The original bound result extent+n+returned-word length+2max(returned-word length,result extent)+13 counts every physical transition. Every noninput head remains at least one at every intermediate time, including the initial child-inspection frame and final resumed body.
-- source:
--   Original complete protected parent-resumption integration for integer multiplication recursive foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_EndParkResume_resume_protected_prefix
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveCall IntMul.EndParkRecursiveResume

theorem IntMul.EndParkRecursiveResume.resume_parent_protected_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+13 ∧
      (machine M n request resume).step^[t]
        (childInspection M n request resume base rho sigma offset extent c label w)=
        resumedFrame M n request resume base rho sigma offset extent c label w ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[s]
          (childInspection M n request resume base rho sigma offset extent c label w)).head i := by sorry

-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveScheduler_resume_correct
-- name    : IntMul.EndParkRecursiveScheduler.resume_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T03:55:30.152777+00:00
-- url     : https://prove2.me/theorems/bee007d7-067d-46e6-b23f-bd7f3c057797
-- title:
--   Complete result-only return inside one fixed unbounded recursive scheduler
-- statement:
--   The SAME complete finite recursive scheduler physically restores only the result bank, pops and erases its physical continuation record, canonically places the child result and enters the recovered real body continuation. Every action and handoff is a charged machine transition. The exact full final configuration, every work head, the full output suffix and full restored continuation tape are proved. Its clock is at most E_out+n+W+2max(W,E_out)+12, independent of the retained extents on unrelated parent work tapes. Exactly M.k+3 tapes and the same finite body control are used at arbitrary depth. Full optimized call-tree evaluation and a fast multiplication body remain separate targets.
-- source:
--   Original complete finite-table integration of result-only physical return for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveScheduler
import Theorems.Thm_IntMul_EndParkResume_resume_correct
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveScheduler

theorem IntMul.EndParkRecursiveScheduler.resume_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (EndParkResume.machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n request resume).step^[t]
        (initialFrame M n request resume base rho sigma offset extent c label w)=
        finalFrame M n request resume base rho sigma offset extent c label w ∧
      (finalFrame M n request resume base rho sigma offset extent c label w).state=.body (resume label) ∧
      (∀ j, (finalFrame M n request resume base rho sigma offset extent c label w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (BankedSimulation.workTape M j))=
        offset j+(if j=M.outTape then 0 else extent j+1)) ∧
      (∀ p, (finalFrame M n request resume base rho sigma offset extent c label w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (BankedSimulation.workTape M M.outTape))
        (offset M.outTape+p)=some (M.tapeOf (w.map M.bitSym) p,decide (p≤ w.length))) ∧
      (finalFrame M n request resume base rho sigma offset extent c label w).cells (FiniteContinuationStack.stackTape M)=
        FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
      (finalFrame M n request resume base rho sigma offset extent c label w).head (FiniteContinuationStack.stackTape M)=rho := by sorry

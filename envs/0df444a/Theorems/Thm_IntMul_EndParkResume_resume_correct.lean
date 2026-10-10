-- Prove2me | Theorems.Thm_IntMul_EndParkResume_resume_correct
-- name    : IntMul.EndParkResume.resume_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T03:40:48.374276+00:00
-- url     : https://prove2.me/theorems/7fd671bc-6ede-49da-8077-bd23e5253d2a
-- title:
--   Complete physical parent return without rewinding unaffected work banks
-- statement:
--   Consider a saved parent invocation whose result bank has visited extent e, with unique local markers on every parent work bank and a blank unvisited result tail. After child cleanup, the work heads stand at the fresh suffixes beyond the retained parent extents, the shared buffer holds a returned bit word of length W, and the actual continuation tape holds the saved finite label q from a fixed label set of size N. One deterministic finite physical return table restores only the parent result head, physically pops and erases the continuation record, recovers q, places the returned word into the parent result bank, clears any longer old result tail and enters the finite ready control q. Its real clock is at most e+N+W+2 max(W,e)+12. The entire final configuration is exact. Every non-result work head remains at its original fresh-suffix position, the result head is at its parent marker, its entire result suffix is canonical with visited extent W, and the continuation tape is restored to its fresh suffix and original boundary. The same finite visited-bit alphabet and exactly k+3 tapes work at arbitrary older continuation depths and bank offsets. No other parent-bank extent occurs in the bound. Every restore, label read/erase, output transfer, tail clearing and phase dispatch is an actual charged transition. The protocol starts from the specified complete post-child-cleanup layout; child evaluation/cleanup and integration into an optimized full recursive scheduler remain separate.
-- source:
--   Original complete result-only physical parent-return proof for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkResume
import Theorems.Thm_IntMul_TrackedSelectiveParentRestore_restore_correct
import Theorems.Thm_IntMul_TrackedParentOutputBridge_output_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Tactic

open IntMul IntMul.EndParkResume
open IntMul.BankedSimulation (workTape)
open IntMul.FiniteContinuationStack (stackTape)

theorem IntMul.EndParkResume.resume_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n).step^[t] (initialFrame M n base rho sigma offset extent c label w)=
        finalFrame M n base rho sigma offset extent c label w ∧
      (finalFrame M n base rho sigma offset extent c label w).state=.ready label ∧
      (∀ j, (finalFrame M n base rho sigma offset extent c label w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
        offset j+(if j=M.outTape then 0 else extent j+1)) ∧
      (∀ p, (finalFrame M n base rho sigma offset extent c label w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape))
        (offset M.outTape+p)=some (M.tapeOf (w.map M.bitSym) p,decide (p ≤ w.length))) ∧
      (finalFrame M n base rho sigma offset extent c label w).cells (stackTape M)=
        FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho ∧
      (finalFrame M n base rho sigma offset extent c label w).head (stackTape M)=rho := by sorry

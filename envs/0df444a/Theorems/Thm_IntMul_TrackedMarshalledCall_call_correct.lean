-- Prove2me | Theorems.Thm_IntMul_TrackedMarshalledCall_call_correct
-- name    : IntMul.TrackedMarshalledCall.call_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T01:12:47.160991+00:00
-- url     : https://prove2.me/theorems/01bcd4a7-2240-4b6b-a2f2-3f4697febe26
-- title:
--   Complete physical request, saved child execution and parent result placement on a fixed tape set
-- statement:
--   Suppose a tracked parent output bank physically contains x#y, parent heads stay within their visited extents, genuine blank tails follow those extents, and each bank has its unique local marker. The shared caller buffer initially contains an earlier returned word v and the continuation stack has an arbitrary older prefix. If the fixed child machine M halts in T steps with canonical bit word w, the single combined table performs the entire physical child call and returns to the saved finite label q. Its bound includes the actual input-copy time, complete saved child-call time, actual parent result-placement time and all three outer dispatches. The theorem proves the complete final configuration, recovered q, exact entire restored stack and head, canonical parent output with precisely the visited prefix through |w| and a fresh blank suffix, every other parent bank unchanged, every parent work head restored to its retained marker, and the exact returned shared buffer and its head. All handoff equalities are derived from the accepted physical service contracts, rather than assumed as opaque pre-copied-input or restored-tape premises. A genuinely unbounded recursive scheduler, fast multiplication body and campaign kappa roots remain separate work.
-- source:
--   Original physically marshalled saved caller for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedMarshalledCall
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_correct
import Theorems.Thm_IntMul_TrackedParentOutputBridge_output_correct
import Theorems.Thm_IntMul_SavedContinuationCall_call_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Tactic

open IntMul IntMul.TrackedMarshalledCall
open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

theorem IntMul.TrackedMarshalledCall.call_correct (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool)
    (near : ∀ j, c.head j ≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state=M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T+5*span M (extents M (M.initCfg x y) (initialExtent M x y) T)+
        2*(inputWord M x y).length+2*span M extent+2*n+
        max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        w.length+2*max w.length (extent M.outTape)+36 ∧
      (machine M n initial).step^[t] (initialFrame M n initial q base rho sigma offset extent c v)=
        finalFrame M n initial q base rho sigma offset extent c v x y T w ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).state=.inr (.inr (.inr (.inl q))) ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells (FiniteContinuationStack.stackTape M)=
        FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).head (FiniteContinuationStack.stackTape M)=rho ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape))=
        TrackedBankPreparation.bankTape M
          ((initialFrame M n initial q base rho sigma offset extent c v).cells
            (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M M.outTape)))
          (offset M.outTape) (w.map M.bitSym) ∧
      (∀ p, (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape)) (offset M.outTape+p)=
          some (M.tapeOf (w.map M.bitSym) p,decide (p ≤ w.length))) ∧
      (∀ j, (finalFrame M n initial q base rho sigma offset extent c v x y T w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=offset j) ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (TrackedChildInputBridge.bufferTape M))=
        TrackedOutputReturn.bufferTape M
          (base.cells (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (TrackedChildInputBridge.bufferTape M))) sigma w ∧
      (finalFrame M n initial q base rho sigma offset extent c v x y T w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (TrackedChildInputBridge.bufferTape M))=sigma+w.length+1 ∧
      (∀ j, j ≠ M.outTape → (finalFrame M n initial q base rho sigma offset extent c v x y T w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
        (initialFrame M n initial q base rho sigma offset extent c v).cells
          (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j))) := by sorry

-- Prove2me | Theorems.Thm_IntMul_TrackedParentOutputBridge_output_correct
-- name    : IntMul.TrackedParentOutputBridge.output_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T00:37:49.762192+00:00
-- url     : https://prove2.me/theorems/8510f603-1c7c-45fb-ad44-34cded63140e
-- title:
--   Physical child-result placement with exact clock, fresh parent output tail and complete preservation of other tapes
-- statement:
--   Suppose the shared caller buffer already physically contains the returned bit word w, with its head just after that word, and the parent output bank head is at its retained local marker. Let W=|w| and E be the old visited output extent, with genuinely blank parent cells beyond E. One fixed five-state machine performs the complete exact run in W+2max(W,E)+5 transitions. Its final parent output bank is the canonical word w with exactly the visited prefix through W and a completely fresh blank tail; its output head is physically restored to the parent boundary. The caller buffer and its head remain exact, as do every other parent bank, visited flag, head and ancestor prefix. The complete final configuration and designated halt are exact. The old output payload need not already be a canonical word: any excess visited blank tail is physically erased as well. A full unbounded recursive multiplication scheduler and fast multiplication body remain separate requirements.
-- source:
--   Original physical parent-output bridge for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedParentOutputBridge
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.TrackedParentOutputBridge

theorem IntMul.TrackedParentOutputBridge.output_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym)
    (tail : ∀ p, extent M.outTape<p → c.cells M.outTape p=M.blank) :
    (machine M).step^[w.length+2*max w.length (extent M.outTape)+5]
      (initialFrame M base sigma offset extent c w) = finalFrame M base sigma offset extent c w ∧
    (finalFrame M base sigma offset extent c w).state = (machine M).qHalt ∧
    (finalFrame M base sigma offset extent c w).cells (targetTape M) =
      TrackedBankPreparation.bankTape M (base.cells (targetTape M)) (offset M.outTape) (w.map M.bitSym) ∧
    (∀ p, (finalFrame M base sigma offset extent c w).cells (targetTape M) (offset M.outTape+p)=
      some (M.tapeOf (w.map M.bitSym) p,decide (p≤w.length))) ∧
    (finalFrame M base sigma offset extent c w).head (targetTape M) = offset M.outTape ∧
    (finalFrame M base sigma offset extent c w).cells (bufferTape M) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
    (finalFrame M base sigma offset extent c w).head (bufferTape M) = sigma+w.length+1 ∧
    (∀ i, i≠targetTape M → (finalFrame M base sigma offset extent c w).cells i =
      (initialFrame M base sigma offset extent c w).cells i) ∧
    (∀ i, i≠targetTape M → (finalFrame M base sigma offset extent c w).head i =
      (initialFrame M base sigma offset extent c w).head i) := by sorry

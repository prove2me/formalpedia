-- Prove2me | Theorems.Thm_IntMul_TrackedReturnReplacement_return_correct
-- name    : IntMul.TrackedReturnReplacement.return_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T01:24:50.429893+00:00
-- url     : https://prove2.me/theorems/e2b80ad9-cb55-493a-8bf4-b1c141049565
-- title:
--   Complete physical replacement of an old shared return word by a new output-bank result
-- statement:
--   Suppose the current output bank contains a canonical returned bit word w and the shared caller buffer contains an older bit word v with its head just after that older result. One fixed finite machine performs a complete actual run in at most max(source head,|v|+1)+2max(|w|,|v|)+|w|+6 transitions. Its entire final buffer is exactly w with its retained local marker, visited prefix and completely fresh suffix, and its head is just after w. The source bank head is physically restored to its marker. Every source-bank cell and flag, every other work bank and every other work head is retained. The complete final configuration and designated halt are exact. The theorem includes empty and shorter replacements and physically erases all excess old-buffer cells. This is a reusable recursive return prerequisite; it does not assert full scheduler or fast multiplication correctness.
-- source:
--   Original recursive result-buffer replacement for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedReturnReplacement
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.TrackedReturnReplacement

theorem IntMul.TrackedReturnReplacement.return_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
    (packet : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+6 ∧
      (machine M).step^[t] (initialFrame M base sigma offset extent c v)=
        finalFrame M base sigma offset extent c v w ∧
      (finalFrame M base sigma offset extent c v w).state=(machine M).qHalt ∧
      (finalFrame M base sigma offset extent c v w).cells (bufferTape M)=
        TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
      (finalFrame M base sigma offset extent c v w).head (bufferTape M)=sigma+w.length+1 ∧
      (∀ j, (finalFrame M base sigma offset extent c v w).cells (BankedSimulation.workTape M j)=
        (initialFrame M base sigma offset extent c v).cells (BankedSimulation.workTape M j)) ∧
      (∀ j, (finalFrame M base sigma offset extent c v w).head (BankedSimulation.workTape M j)=
        if j=M.outTape then offset j else offset j+c.head j) := by sorry

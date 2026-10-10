-- Prove2me | Theorems.Thm_IntMul_TrackedChildInputBridge_input_correct
-- name    : IntMul.TrackedChildInputBridge.input_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T00:27:09.385898+00:00
-- url     : https://prove2.me/theorems/fa11b9e5-0603-4505-b8e4-baf6926ae35e
-- title:
--   Physical parent-request input bridge with exact clock, complete tape preservation and restored heads
-- statement:
--   Suppose a tracked parent output bank already physically contains the canonical child argument packet x#y, with source head a, and the shared caller buffer contains an earlier returned bit word v with its head just after that word. Let L=|x|+|y|+1, B=|v|, A=max(a,B+1), and H=max(L,B). One fixed five-state machine performs the exact complete run in A+2H+4 actual transitions. The final buffer is exactly the child source tape for x#y, with its head at the retained boundary, and satisfies the self-consistent source premise required by the complete child caller. Every parent bank cell and visited flag remains exactly equal to its initial configuration. The packet-bank head is physically rewound to its parent boundary; every other parent work head remains unchanged. The complete final configuration and designated halt are exact. Old-buffer tails are physically erased even when the replacement packet is shorter. The parent must still compute the request packet beforehand; an unbounded recursive multiplication scheduler remains separate work.
-- source:
--   Original physical child-input bridge for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedChildInputBridge
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.TrackedChildInputBridge
open IntMul.TrackedBankPreparation (inputWord)

theorem IntMul.TrackedChildInputBridge.input_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (x y : List Bool) (packet : c.cells M.outTape = M.tapeOf (inputWord M x y)) :
    (machine M).step^[max (c.head M.outTape) (v.length+1) + 2*max (inputWord M x y).length v.length + 4]
      (initialFrame M base sigma offset extent c v) = finalFrame M base sigma offset extent c v x y ∧
    (finalFrame M base sigma offset extent c v x y).state = (machine M).qHalt ∧
    (finalFrame M base sigma offset extent c v x y).cells (bufferTape M) =
      TrackedBankPreparation.sourceTape M (base.cells (bufferTape M)) sigma (inputWord M x y) ∧
    (finalFrame M base sigma offset extent c v x y).cells (bufferTape M) =
      TrackedBankPreparation.sourceTape M
        ((finalFrame M base sigma offset extent c v x y).cells (bufferTape M)) sigma (inputWord M x y) ∧
    (finalFrame M base sigma offset extent c v x y).head (bufferTape M) = sigma ∧
    (∀ j, (finalFrame M base sigma offset extent c v x y).cells (BankedSimulation.workTape M j) =
      (initialFrame M base sigma offset extent c v).cells (BankedSimulation.workTape M j)) ∧
    (∀ j, (finalFrame M base sigma offset extent c v x y).head (BankedSimulation.workTape M j) =
      if j=M.outTape then offset j else offset j+c.head j) := by sorry

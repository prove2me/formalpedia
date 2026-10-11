-- Prove2me | Theorems.Thm_IntMul_PreparedBankedCall_call_prepared
-- name    : IntMul.PreparedBankedCall.call_prepared
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T14:08:32.097021+00:00
-- url     : https://prove2.me/theorems/96ded450-046e-419f-8ed0-3faa313b544e
-- title:
--   Complete prepared-state banked execution and global output return with retained caller input
-- statement:
--   Let $M$ be a deterministic fixed multitape machine, and let $c$ be an explicitly supplied child configuration whose local tapes have their start markers. Suppose $M$ halts from $c$ within $T$ transitions and its terminal output is the binary word $w$. Write $H$ for its terminal output-head position. A fixed banked caller executes this prepared child configuration on writable work banks and physically returns the output to global output in at most
--
--   $$T+H+|w|+3$$
--
--   actual transitions. It reaches the exact complete returned caller configuration, globally halts, preserves the original read-only caller input tape and head, and retains every cell-zero work-bank prefix. The terminal native bank contents are specified completely by the returned frame. The theorem allows padded child clocks and arbitrary prepared child states. Preparing the child banks and the incoming empty global-output tape and cursor remains an explicit caller obligation.
-- source:
--   Original arbitrary-prepared-state generalization of the accepted banked caller. Owns first-halt simulation, physical rewind, bit-by-bit output return, complete terminal frame and retained input/prefix proofs. Written by Codex.

import Definitions.Def_IntMul_PreparedBankedCall
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop

open IntMul IntMul.PreparedBankedCall

theorem IntMul.PreparedBankedCall.call_prepared (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0=M.startSym)
    (halt : (M.step^[T] c).state=M.qHalt) (w : List Bool)
    (out : (M.step^[T] c).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t : ℕ, t ≤ T+(M.step^[T] c).head M.outTape+w.length+3 ∧
      (machine M).step^[t] (runningFrame M base c)=finalFrame M base (M.step^[T] c) w ∧
      ((machine M).step^[t] (runningFrame M base c)).state=(machine M).qHalt ∧
      ((machine M).step^[t] (runningFrame M base c)).cells (machine M).outTape=
        (machine M).tapeOf (w.map (machine M).bitSym) ∧
      ((machine M).step^[t] (runningFrame M base c)).cells (machine M).inTape=base.cells (machine M).inTape ∧
      ((machine M).step^[t] (runningFrame M base c)).head (machine M).inTape=base.head (machine M).inTape ∧
      (∀ j, ((machine M).step^[t] (runningFrame M base c)).cells (BankedSimulation.workTape M j) 0=
        base.cells (BankedSimulation.workTape M j) 0) := by sorry

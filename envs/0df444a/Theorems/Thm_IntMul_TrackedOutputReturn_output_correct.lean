-- Prove2me | Theorems.Thm_IntMul_TrackedOutputReturn_output_correct
-- name    : IntMul.TrackedOutputReturn.output_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T22:26:20.461488+00:00
-- url     : https://prove2.me/theorems/73adbf32-9af0-4161-99c6-92ef947865d4
-- title:
--   Complete physical output return with independent head rewinds and unchanged workspace flags
-- statement:
--   For arbitrary prepared tracked child banks whose output is the canonical tape for word w, and a prepared empty caller buffer, exactly max(bufferHeadDistance,childOutputHeadDistance)+length(w)+2 actual transitions return the complete output to the caller buffer and halt. The two rewind heads stop independently at their own markers. Every child-bank symbol and visited flag is retained, as are the root input and all earlier prefixes. The returned buffer contains its saved prefix, local marker, the exact word and a fresh blank tail; its head and the child output head are on their end blanks. Empty and leading-zero words are included. This enables subsequent workspace cleanup without erasing the caller's result. Buffer/marker preparation, child computation, cleanup and recursive scheduling are separate obligations.
-- source:
--   Original physical tracked output-return construction for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_TrackedOutputReturn
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)

open IntMul IntMul.TrackedOutputReturn

theorem IntMul.TrackedOutputReturn.output_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    (machine M).step^[max a b + w.length + 2] (returnFrame M base sigma offset extent c a b) =
      finalFrame M base sigma offset extent c w := by sorry

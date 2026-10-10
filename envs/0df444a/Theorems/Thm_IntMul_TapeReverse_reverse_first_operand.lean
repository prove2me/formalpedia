-- Prove2me | Theorems.Thm_IntMul_TapeReverse_reverse_first_operand
-- name    : IntMul.TapeReverse.reverse_first_operand
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T09:13:29.356706+00:00
-- url     : https://prove2.me/theorems/f991490f-8a83-4cfd-a5d4-c01fe4e186b0
-- title:
--   Actual two-tape word reversal in exactly 2n+3 transitions
-- statement:
--   For arbitrary binary operands x,y, the fixed two-tape, five-symbol, four-state reversal machine halts with exact output reverse(x) in 2|x|+3 actual transitions. It leaves the entire input x#y unchanged, the input head at the original start marker, the output head just after reverse(x), and the complete final configuration equal to the specified frame. Empty words and arbitrary second operands are included. Scanning to the delimiter, changing direction, all reverse-copy steps and halting are charged; the table uses only finite state and scanned symbols.
-- source:
--   Original fixed-tape word reversal for least-significant-first digit routing in the integer multiplication construction. Written by Codex.

import Definitions.Def_IntMul_TapeReverse
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

open IntMul.TapeReverse

theorem IntMul.TapeReverse.reverse_first_operand (x y : List Bool) :
    machine.HaltsWithOutput x y (2*x.length+3) x.reverse ∧
      machine.step^[2*x.length+3] (machine.initCfg x y)=frame x y 0 .halt := by sorry

-- Prove2me | Theorems.Thm_IntMul_BinarySchoolbook_product_word_correct
-- name    : IntMul.BinarySchoolbook.product_word_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T20:00:22.87231+00:00
-- url     : https://prove2.me/theorems/8f25e9de-3fef-4fef-ab00-0d7c7aba1912
-- title:
--   Exact fixed-width shift-and-add word multiplication, including leading zeros
-- statement:
--   For any equal-length binary words x and y, the explicit fixed-width Horner shift-and-add word algorithm returns exactly bin(2|x|,val(x)*val(y)). The accumulator has width 2|x| throughout; intermediate shifts and additions discard high carries and are analyzed modulo 2^(2|x|). The final exact product is below this capacity, so the output retains every required leading zero. Empty words are included. This theorem supplies the arithmetic interface for the actual schoolbook tape machine; it does not by itself prove any Turing-machine time bound.
-- source:
--   Classical shift-and-add algorithm used in the existing IntMul.TM.schoolbook milestone (86109c88-e1e4-410a-a312-0a5f005a04cf). Original fixed-width word and machine interface formalization, Written by Codex.

import Definitions.Def_IntMul_BinarySchoolbook
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

open IntMul.BinarySchoolbook

theorem IntMul.BinarySchoolbook.product_word_correct (x y : List Bool) (h : x.length = y.length) :
    productWord x y = IntMul.bin (2 * x.length) (IntMul.val x * IntMul.val y) := by sorry

-- Prove2me | Theorems.Thm_N4Code_testBit2_of_le7
-- name    : N4Code.testBit2_of_le7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:09.172906+00:00
-- url     : https://prove2.me/theorems/27d740fa-21bf-5996-9a63-7b66e25bd0c0
-- title:
--   N4 Code: test Bit2 of le7
-- statement:
--   For n ≤ 7, bit 2 of n is 1 exactly for types 4..7.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2011-L2016
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2011-L2016

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.testBit2_of_le7 (n : ℕ) (hn : n ≤ 7) :
    (n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7) ↔ n.testBit 2 = true := by sorry

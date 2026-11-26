-- Prove2me | Theorems.Thm_N4Code_sum_Icc0_7
-- name    : N4Code.sum_Icc0_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:25.553171+00:00
-- url     : https://prove2.me/theorems/daced2e6-a381-5124-9e15-c747a8361293
-- title:
--   N4 Code: sum Icc0 7
-- statement:
--   Sum over the type range 0..7.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1119-L1132
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1119-L1132

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.sum_Icc0_7 (f : ℕ → ℕ) : (∑ i ∈ Finset.Icc 0 7, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by sorry

-- Prove2me | Theorems.Thm_N4Code_sum_mod_two
-- name    : N4Code.sum_mod_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:50.00824+00:00
-- url     : https://prove2.me/theorems/2d3eb8f2-4a73-54b8-a598-77f1026064a1
-- title:
--   N4 Code: sum mod two
-- statement:
--   Sums are additive modulo two.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1894-L1901
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1894-L1901

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.sum_mod_two {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ t ∈ s, f t) % 2 = (∑ t ∈ s, f t % 2) % 2 := by sorry

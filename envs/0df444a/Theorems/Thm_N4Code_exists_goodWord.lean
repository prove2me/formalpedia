-- Prove2me | Theorems.Thm_N4Code_exists_goodWord
-- name    : N4Code.exists_goodWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:13.295468+00:00
-- url     : https://prove2.me/theorems/53dadf0b-f4e7-5b9e-a353-0040b6882d22
-- title:
--   N4 Code: exists good Word
-- statement:
--   A word with the prescribed per-type weights, when they are feasible.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1072-L1083
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1072-L1083

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.exists_goodWord {n : ℕ} (C : Code n) (k : ℕ → ℕ)
    (hk : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i) :
    ∃ y : Word n, ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by sorry

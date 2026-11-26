-- Prove2me | Theorems.Thm_N4Code_even_pair
-- name    : N4Code.even_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:56.839929+00:00
-- url     : https://prove2.me/theorems/e277ee5e-cd9b-5ba7-952f-d4c158236270
-- title:
--   N4 Code: even pair
-- statement:
--   Among the four codewords there are two at even distance.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1933-L1966
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1933-L1966

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.even_pair {n : ℕ} (C : Code n) : ∃ i j : Fin 4, i ≠ j ∧
    Even (hammingDist (row C i) (row C j)) := by sorry

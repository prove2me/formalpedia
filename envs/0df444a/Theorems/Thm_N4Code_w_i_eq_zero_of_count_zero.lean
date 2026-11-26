-- Prove2me | Theorems.Thm_N4Code_w_i_eq_zero_of_count_zero
-- name    : N4Code.w_i_eq_zero_of_count_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:04.689232+00:00
-- url     : https://prove2.me/theorems/9c52402d-3b49-5fa4-b260-d2c1b61df8dc
-- title:
--   N4 Code: w i eq zero of count zero
-- statement:
--   The per-type weight vanishes when the type does not occur.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L608-L615
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L608-L615

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.w_i_eq_zero_of_count_zero {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) (h : count C i = 0) :
    w_i C i y = 0 := by sorry

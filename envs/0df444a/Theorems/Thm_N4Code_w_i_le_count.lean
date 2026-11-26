-- Prove2me | Theorems.Thm_N4Code_w_i_le_count
-- name    : N4Code.w_i_le_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:39.784991+00:00
-- url     : https://prove2.me/theorems/33929c1c-c097-4390-8471-cfa9e2d0ece9
-- title:
--   N4 Code: w i le count
-- statement:
--   The per-type weight is at most the per-type count.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L601-L605
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L601-L605

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.w_i_le_count {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) : w_i C i y ≤ count C i := by sorry

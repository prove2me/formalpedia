-- Prove2me | Theorems.Thm_N4Code_dRowMin_ge_one
-- name    : N4Code.dRowMin_ge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:35.585106+00:00
-- url     : https://prove2.me/theorems/ed9fcdc2-91be-4a30-a2ad-ab1bc5733c91
-- title:
--   N4 Code: d Row Min ge one
-- statement:
--   Every row distance is at least one when y has bit 1 at a zero column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L337-L357
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L337-L357

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRowMin_ge_one {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (t : Fin n) (y : Word n) (hcol : C t = col0) (hyt : y t = true) :
    1 ≤ dRowMin C S hS y := by sorry

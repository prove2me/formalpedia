-- Prove2me | Theorems.Thm_N4Code_colWeight_eq_two_iff_C0form
-- name    : N4Code.colWeight_eq_two_iff_C0form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:12.296323+00:00
-- url     : https://prove2.me/theorems/8e682fb7-c8ff-4202-8bc9-aa88cf4e42db
-- title:
--   N4 Code: col Weight eq two iff C0form
-- statement:
--   In a C0-form code, weight 2 exactly means type 5 or 6.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2728-L2754
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2728-L2754

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colWeight_eq_two_iff_C0form {n : ℕ} (C : Code n) (h : C0form C) (t : Fin n) :
    colWeight (C t) = 2 ↔ colVal (C t) = 5 ∨ colVal (C t) = 6 := by sorry

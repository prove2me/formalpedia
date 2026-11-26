-- Prove2me | Theorems.Thm_N4Code_C0form_types
-- name    : N4Code.C0form_types
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:03.558629+00:00
-- url     : https://prove2.me/theorems/14ae874a-bc5c-551a-8fee-c8c6a8c40638
-- title:
--   N4 Code: C0form types
-- statement:
--   In a C0-form code every column has type 0, 5, or 6.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2684-L2724
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2684-L2724

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.C0form_types {n : ℕ} (C : Code n) (h : C0form C) (t : Fin n) :
    colVal (C t) = 0 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by sorry

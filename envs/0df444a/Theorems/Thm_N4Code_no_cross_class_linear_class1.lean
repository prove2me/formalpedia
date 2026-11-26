-- Prove2me | Theorems.Thm_N4Code_no_cross_class_linear_class1
-- name    : N4Code.no_cross_class_linear_class1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:48.273845+00:00
-- url     : https://prove2.me/theorems/39d36c75-1f5d-4330-9a09-23fb1dd17a8e
-- title:
--   N4 Code: no cross class linear class1
-- statement:
--   No linear code is equivalent to a Class-I code.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L437-L439
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L437-L439

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.no_cross_class_linear_class1 {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hC' : ClassI C') :
    ¬ Equivalent C C' := by sorry

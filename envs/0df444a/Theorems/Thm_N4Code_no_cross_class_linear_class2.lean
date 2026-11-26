-- Prove2me | Theorems.Thm_N4Code_no_cross_class_linear_class2
-- name    : N4Code.no_cross_class_linear_class2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:49.308566+00:00
-- url     : https://prove2.me/theorems/e4922bf4-41a2-5f6b-afbe-97933537ebfb
-- title:
--   N4 Code: no cross class linear class2
-- statement:
--   No linear code is equivalent to a Class-II code.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L442-L444
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L442-L444

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

theorem N4Code.no_cross_class_linear_class2 {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hC' : ClassII C') :
    ¬ Equivalent C C' := by sorry

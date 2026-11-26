-- Prove2me | Theorems.Thm_N4Code_linear_not_equiv_weight1
-- name    : N4Code.linear_not_equiv_weight1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:47.677808+00:00
-- url     : https://prove2.me/theorems/a4417ab7-3093-4c9a-87a3-b1fdc4e230b6
-- title:
--   N4 Code: linear not equiv weight1
-- statement:
--   No linear code is equivalent to a code with a type-1 column
--   (Class-I, Class-II, or Class-III all have |1| > 0).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L419-L423
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L419-L423

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

theorem N4Code.linear_not_equiv_weight1 {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hpos : count C' 1 > 0) :
    ¬ Equivalent C C' := by sorry

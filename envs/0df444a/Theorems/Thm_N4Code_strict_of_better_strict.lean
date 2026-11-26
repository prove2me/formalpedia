-- Prove2me | Theorems.Thm_N4Code_strict_of_better_strict
-- name    : N4Code.strict_of_better_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:20.532935+00:00
-- url     : https://prove2.me/theorems/181891ce-162f-410f-bc02-1e2bf003c74b
-- title:
--   N4 Code: strict of better strict
-- statement:
--   Better then strictly better is strictly better.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2832-L2836
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2832-L2836

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.strict_of_better_strict {n : ℕ} (C₁ C₂ C₃ : Code n)
    (h12 : UniversalBetter C₁ C₂) (h23 : UniversalStrictBetter C₂ C₃) :
    UniversalStrictBetter C₁ C₃ := by sorry

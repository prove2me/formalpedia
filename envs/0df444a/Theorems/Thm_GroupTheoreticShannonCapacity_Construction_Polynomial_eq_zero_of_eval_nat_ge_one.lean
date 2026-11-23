-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_Polynomial_eq_zero_of_eval_nat_ge_one
-- name    : GroupTheoreticShannonCapacity.Construction.Polynomial.eq_zero_of_eval_nat_ge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:35:06.867023+00:00
-- url     : https://prove2.me/theorems/3733628f-eeaf-4f0c-8746-5031094b06f8
-- title:
--   Polynomial: eq zero of eval nat ge one
-- statement:
--   A polynomial over ℚ that vanishes on all natural numbers ≥ 1 is zero.
--       This follows from Polynomial.finite_setOf_isRoot: a nonzero polynomial has
--       finitely many roots, but {1, 2, 3, ...} is infinite.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1718-L1742
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1718-L1742

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.Polynomial.eq_zero_of_eval_nat_ge_one (P : Polynomial ℚ)
    (h : ∀ s : ℕ, s ≥ 1 → P.eval (s : ℚ) = 0) : P = 0 := by sorry

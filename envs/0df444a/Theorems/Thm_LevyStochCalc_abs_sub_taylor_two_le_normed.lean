-- Prove2me | Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le_normed
-- name    : LevyStochCalc.abs_sub_taylor_two_le_normed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:43:07.195141+00:00
-- url     : https://prove2.me/theorems/c25de4ae-be1a-4f51-b30d-42048aa93a80
-- title:
--   abs sub taylor two le normed
-- statement:
--   The source theorem `LevyStochCalc.abs_sub_taylor_two_le_normed` is extracted from `LevyStochCalc.Brownian.TaylorTwoVector`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F000
import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F001
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The second-order Taylor bound on a normed space

For a real function on a normed space whose second derivative is Lipschitz, the second-order
Taylor remainder at a point is cubic in the increment. The bound follows from the scalar case
along the segment joining the two points.

## Main statements

* `LevyStochCalc.abs_sub_taylor_two_le_normed` — the pointwise cubic bound.
* `LevyStochCalc.taylorRemainderNormed` — the remainder along a sequence.
-/

namespace LevyStochCalc

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem _root_.LevyStochCalc.abs_sub_taylor_two_le_normed {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ K * ‖z - w‖) (x y : E) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2| ≤ K * ‖y - x‖ ^ 3 := by sorry

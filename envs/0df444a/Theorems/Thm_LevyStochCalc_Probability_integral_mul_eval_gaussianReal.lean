-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_mul_eval_gaussianReal
-- name    : LevyStochCalc.Probability.integral_mul_eval_gaussianReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:12:09.421825+00:00
-- url     : https://prove2.me/theorems/a71f8786-3920-452a-b8b7-040d9d2cef5e
-- title:
--   integral mul eval gaussianReal
-- statement:
--   The source theorem `LevyStochCalc.Probability.integral_mul_eval_gaussianReal` is extracted from `LevyStochCalc.Probability.GaussianMoments`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_GaussianMoments_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a centred real Gaussian and Gaussian integration by parts

For the law `gaussianReal 0 v` on `ℝ` the even moments are `E[X^(2n)] = v^n (2n-1)!!`, the odd
moments vanish, and the two are tied together by the recursion `E[X^(k+2)] = (k+1) v E[X^k]`.
Every polynomial function is integrable for this law, and the Stein identity
`E[X p(X)] = v E[p'(X)]` holds for every real polynomial `p`.

## Main statements

* `LevyStochCalc.Probability.integral_pow_even_gaussianReal` — `E[X^(2n)] = v^n (2n-1)!!`.
* `LevyStochCalc.Probability.integral_pow_odd_gaussianReal` — `E[X^(2n+1)] = 0`.
* `LevyStochCalc.Probability.integral_pow_add_two_gaussianReal` — `E[X^(k+2)] = (k+1) v E[X^k]`.
* `LevyStochCalc.Probability.integrable_eval_gaussianReal` — `p(X)` is integrable.
* `LevyStochCalc.Probability.integral_mul_eval_gaussianReal` — `E[X p(X)] = v E[p'(X)]`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

variable (v : ℝ≥0)

theorem _root_.LevyStochCalc.Probability.integral_mul_eval_gaussianReal (p : ℝ[X]) :
    ∫ x, x * p.eval x ∂gaussianReal 0 v
      = (v : ℝ) * ∫ x, (derivative p).eval x ∂gaussianReal 0 v := by sorry

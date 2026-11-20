-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_hermitePoly_mul
-- name    : LevyStochCalc.Probability.integral_hermitePoly_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:29:43.5549+00:00
-- url     : https://prove2.me/theorems/1bd5dac8-2091-44f9-835d-187cfc357041
-- title:
--   integral hermitePoly mul
-- statement:
--   The source theorem `LevyStochCalc.Probability.integral_hermitePoly_mul` is extracted from `LevyStochCalc.Probability.Hermite`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Hermite_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Hermite polynomials of variance `v` and their Gaussian orthogonality

The probabilists' Hermite polynomials of variance `v` are given by the Appell recursion
`H_(n+1) = (x - v d/dx) H_n`, which makes the derivative `H_(n+1)' = (n+1) H_n` and the three-term
recursion `H_(n+2) = x H_(n+1) - (n+1) v H_n` immediate. For `v > 0` they rescale Mathlib's
family `Polynomial.hermite` by `H_n(x; v) = √v ^ n * He_n(x / √v)`, and `H_2(x; v) = x ^ 2 - v`.
Under the law `gaussianReal 0 v` they are orthogonal, with `E[H_n H_m] = δ_(n m) n! v ^ n`.

The opening section adds the derivative and the three-term recursion of Mathlib's
`Polynomial.hermite`, both of which belong with `Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`.

## Main statements

* `Polynomial.derivative_hermite` — `He_(n+1)' = (n+1) He_n`.
* `Polynomial.hermite_succ_succ` — `He_(n+2) = X He_(n+1) - (n+1) He_n`.
* `LevyStochCalc.Probability.derivative_hermitePoly` — `H_(n+1)' = (n+1) H_n`.
* `LevyStochCalc.Probability.hermitePoly_succ_succ` — `H_(n+2) = X H_(n+1) - (n+1) v H_n`.
* `LevyStochCalc.Probability.hermiteScaled_two` — `H_2(x; v) = x ^ 2 - v`.
* `LevyStochCalc.Probability.hermiteScaled_eq` — `H_n(x; v) = √v ^ n * He_n(x / √v)` for `v > 0`.
* `LevyStochCalc.Probability.integral_hermitePoly_mul` — `E[H_n H_m] = δ_(n m) n! v ^ n`.
-/

namespace Polynomial

end Polynomial

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

theorem _root_.LevyStochCalc.Probability.integral_hermitePoly_mul (v : ℝ≥0) (n m : ℕ) :
    ∫ x, (hermitePoly (v : ℝ) n).eval x * (hermitePoly (v : ℝ) m).eval x ∂gaussianReal 0 v
      = if n = m then (n.factorial : ℝ) * (v : ℝ) ^ n else 0 := by sorry

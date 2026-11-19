-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_charlierScaled_forward_diff
-- name    : LevyStochCalc.Probability.charlierScaled_forward_diff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:39:46.45985+00:00
-- url     : https://prove2.me/theorems/fcfe0631-5de1-4042-9b45-97f90049a202
-- title:
--   charlierScaled forward diff
-- statement:
--   The source theorem `LevyStochCalc.Probability.charlierScaled_forward_diff` is extracted from `LevyStochCalc.Probability.Charlier`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Charlier_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Charlier polynomials and their Poisson orthogonality

The Charlier polynomials with parameter `lam` are given by the recursion
`C_(s+1)(x) = x C_s(x - 1) - lam C_s(x)` from `C_0 = 1`, the backward-difference analogue of the
Hermite recursion `H_(n+1) = (x - v d/dx) H_n`; their exponential generating function is
`e^(-lam t) (1 + t) ^ x`. The forward difference plays the role the derivative plays there,
`C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)`, and the degree-two member is
`C_2(x; lam) = (x - lam) ^ 2 - x`. The parameter is the mean of the Poisson law that makes the
family orthogonal: under the Poisson law of mean `r` the family with parameter `r` satisfies
`E[C_s C_t] = δ_(s t) s! r ^ s`.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_succ` — the recursion at the level of values.
* `LevyStochCalc.Probability.charlierScaled_two` — `C_2(x; lam) = (x - lam) ^ 2 - x`.
* `LevyStochCalc.Probability.charlierScaled_forward_diff` —
  `C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)`.
* `LevyStochCalc.Probability.integral_charlierPoly_mul` — `E[C_s C_t] = δ_(s t) s! r ^ s`.
* `LevyStochCalc.Probability.integral_charlierPoly_sq` — `E[C_s ^ 2] = s! r ^ s`.
* `LevyStochCalc.Probability.integral_charlierPoly_eq_zero` — `E[C_s] = 0` for `s ≠ 0`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal Nat

theorem _root_.LevyStochCalc.Probability.charlierScaled_forward_diff (s : ℕ) (lam x : ℝ) :
    charlierScaled (s + 1) lam (x + 1) - charlierScaled (s + 1) lam x
      = ((s : ℝ) + 1) * charlierScaled s lam x := by sorry

-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_mul_eval_poissonMeasure
-- name    : LevyStochCalc.Probability.integral_mul_eval_poissonMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:38:32.185961+00:00
-- url     : https://prove2.me/theorems/76eb957f-7ff0-4604-bfda-f515daf440cc
-- title:
--   integral mul eval poissonMeasure
-- statement:
--   The source theorem `LevyStochCalc.Probability.integral_mul_eval_poissonMeasure` is extracted from `LevyStochCalc.Probability.PoissonMoments`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_PoissonMoments_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Poisson law and Poisson integration by parts

The law `poissonMeasure r` on `ℕ` gives the atom `n` the mass `exp (-r) * r ^ n / n !`, so it is
the Poisson law of mean `r`. Every polynomial function is integrable for it, and the Stein
identity `E[N p(N)] = r E[p(N + 1)]` holds for every real polynomial `p`, with the forward shift
in place of the derivative of the Gaussian identity. Mean and variance are both `r`, the
factorial moments are `E[N (N - 1) ⋯ (N - k + 1)] = r ^ k`, the third central moment is `r` and
the fourth central moment is `3 r ^ 2 + r`. The identity has moments of every finite order.

## Main statements

* `LevyStochCalc.Probability.integrable_eval_poissonMeasure` — `p(N)` is integrable.
* `LevyStochCalc.Probability.integral_mul_eval_poissonMeasure` — `E[N p(N)] = r E[p(N + 1)]`.
* `LevyStochCalc.Probability.integral_id_poissonMeasure` — `E[N] = r`.
* `LevyStochCalc.Probability.integral_id_sq_poissonMeasure` — `E[N ^ 2] = r ^ 2 + r`.
* `LevyStochCalc.Probability.integral_sub_sq_poissonMeasure` — `E[(N - r) ^ 2] = r`.
* `LevyStochCalc.Probability.integral_descPochhammer_eval_poissonMeasure` — the factorial
  moments `E[N (N - 1) ⋯ (N - k + 1)] = r ^ k`.
* `LevyStochCalc.Probability.integral_sub_pow_three_poissonMeasure` — `E[(N - r) ^ 3] = r`.
* `LevyStochCalc.Probability.integral_sub_pow_four_poissonMeasure` —
  `E[(N - r) ^ 4] = 3 r ^ 2 + r`.
* `LevyStochCalc.Probability.memLp_natCast_poissonMeasure` — `N ∈ Lᵖ` for every finite `p`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal Nat

theorem _root_.LevyStochCalc.Probability.integral_mul_eval_poissonMeasure (r : ℝ≥0) (p : ℝ[X]) :
    ∫ n : ℕ, (n : ℝ) * p.eval (n : ℝ) ∂poissonMeasure r
      = (r : ℝ) * ∫ n : ℕ, p.eval ((n : ℝ) + 1) ∂poissonMeasure r := by sorry

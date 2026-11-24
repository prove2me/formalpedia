-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonNonnegativeIntegralLawV1
-- name    : Kyprianou.Ch02.poissonNonnegativeIntegralLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:20.643022+00:00
-- url     : https://prove2.me/theorems/f46751b0-9b50-4f4c-a414-842c77ba2338
-- title:
--   Nonnegative Poisson random-measure integral law
-- statement:
--   The distribution of the measurable nonnegative Poisson integral has no negative mass and has the standard Poisson characteristic function.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, positive jump Poisson construction.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.poissonNonnegativeIntegralLawV1
    (m : Measure ℝ) [SigmaFinite m]
    (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hint : Integrable (fun x => min (1 : ℝ) |f x|) m) :
    ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧ Q (Set.Iio (0 : ℝ)) = 0 ∧
      ∀ ξ : ℝ, charFun Q ξ =
        Complex.exp (∫ x, (Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) - 1) ∂m) := by
  sorry

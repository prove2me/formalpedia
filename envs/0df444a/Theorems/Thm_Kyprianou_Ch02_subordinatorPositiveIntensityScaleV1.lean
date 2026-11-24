-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinatorPositiveIntensityScaleV1
-- name    : Kyprianou.Ch02.subordinatorPositiveIntensityScaleV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:27.510881+00:00
-- url     : https://prove2.me/theorems/b4138c20-8760-4920-9e06-b4f934b5619b
-- title:
--   Scaled positive Lévy jump intensity gives a nonnegative law
-- statement:
--   Apply the Poisson integral law to the scaled positive restriction and nonnegative mark max(x,0); identify its characteristic function by scaling and almost-everywhere equality.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, positive jump Poisson construction.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinatorPositiveIntensityScaleV1
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (t : ℝ≥0) :
    ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧ Q (Set.Iio (0 : ℝ)) = 0 ∧
      ∀ ξ : ℝ, charFun Q ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by
  sorry

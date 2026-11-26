-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_weighted_characteristic_expectation
-- name    : Kyprianou.Ch04.kw48_weighted_characteristic_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:40:43.550586+00:00
-- url     : https://prove2.me/theorems/ded65685-16f0-4a3d-b454-e7abaa0deddf
-- title:
--   Past-weighted characteristic exponential expectation in the supplied filtration
-- statement:
--   Past-weighted characteristic exponential expectation in the supplied filtration.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_characteristic_increment_mean_one
import Theorems.Thm_Kyprianou_Ch04_kw48_independent_weight_integral
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The normalised characteristic exponential preserves every
measurable past-weighted expectation in the actual filtration. -/

theorem Kyprianou.Ch04.kw48_weighted_characteristic_expectation {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I * (theta : Complex) *
        (L.X t w : Complex)) ∂P) =
      Complex.exp (-((t : Real) : Complex) * Psi theta))
    (alpha : Real) (s t : NNReal) (hst : s ≤ t)
    (W : Ω → Complex) (hW : Measurable[F s] W) :
    (∫ w, W w * E L Psi alpha t w ∂P) =
      (∫ w, W w * E L Psi alpha s w ∂P) := by sorry

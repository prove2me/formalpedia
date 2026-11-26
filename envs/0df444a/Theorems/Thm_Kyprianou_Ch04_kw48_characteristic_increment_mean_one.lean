-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_characteristic_increment_mean_one
-- name    : Kyprianou.Ch04.kw48_characteristic_increment_mean_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:30:36.439585+00:00
-- url     : https://prove2.me/theorems/bd0a69d6-7639-5822-8197-5af9a00e41fd
-- title:
--   Normalised characteristic future increment has mean one
-- statement:
--   Normalised characteristic future increment has mean one.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The normalised complex future increment has expectation one. -/

theorem Kyprianou.Ch04.kw48_characteristic_increment_mean_one
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I * (theta : Complex) *
        (L.X t w : Complex)) ∂P) =
      Complex.exp (-((t : Real) : Complex) * Psi theta))
    (alpha : Real) (s t : NNReal) (hst : s ≤ t) :
    (∫ w, Complex.exp
      (Complex.I * (alpha : Complex) * ((L.X t w-L.X s w : Real) : Complex) +
        (((t-s : NNReal) : Real) : Complex) * Psi alpha) ∂P) = 1 := by sorry

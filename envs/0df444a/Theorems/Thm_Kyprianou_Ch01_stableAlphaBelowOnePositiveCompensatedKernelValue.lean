-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOnePositiveCompensatedKernelValue
-- name    : Kyprianou.Ch01.stableAlphaBelowOnePositiveCompensatedKernelValue
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:55:02.299144+00:00
-- url     : https://prove2.me/theorems/b5da23f5-cde7-4d89-8a5f-6a1cabddc473
-- title:
--   Exact positive-halfline stable compensated Fourier integral below index one
-- statement:
--   For alpha in (0,1), the positive-jump weighted integral of the exact original compensated Levy integrand equals c Gamma(-alpha)*exp(alpha log(-i xi)) for xi!=0 (and zero otherwise), minus i*c*xi/(1-alpha). The last term is exactly the source small-jump cutoff compensation. This is the key source-exact analytic leaf for the below-one original triplet ledger.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, two-sided stable Levy-Khintchine normal form and source cutoff.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaBelowOnePositiveCompensatedKernelValue
    (alpha c xi : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-alpha - 1)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
      (c : ℂ) *
        (if xi = 0 then 0 else
          ((Real.Gamma (-alpha) : ℝ) : ℂ) *
            Complex.exp ((alpha : ℂ) *
              Complex.log (-(Complex.I * (xi : ℂ))))) -
      Complex.I * (((c * xi / (1 - alpha) : ℝ) : ℂ)) := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOnePositiveCompensatedKernelValue
-- name    : Kyprianou.Ch01.stableAboveOnePositiveCompensatedKernelValue
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T23:49:48.996214+00:00
-- url     : https://prove2.me/theorems/4dae9497-c045-4b4e-aac4-c3b515f3f2e4
-- title:
--   Above-one stable source compensated positive Fourier kernel with exact tail drift
-- statement:
--   For 1<alpha<2, the exact original positive-jump compensated stable Lévy Fourier integral is c Gamma(-alpha)*exp(alpha log(-i xi)) for nonzero frequency, plus the compensating large-jump term i c xi/(alpha-1). At xi=0 the expression vanishes. The source truncation is the indicator of r<1.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4 original above-one stable Lévy triplet.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOnePositiveCompensatedKernelValue
    (alpha c xi : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-alpha - 1)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
      (c : ℂ) *
        (if xi = 0 then 0 else
          ((Real.Gamma (-alpha) : ℝ) : ℂ) *
            Complex.exp ((alpha : ℂ) *
              Complex.log (-(Complex.I * (xi : ℂ))))) +
      Complex.I * (((c * xi / (alpha - 1) : ℝ) : ℂ)) := by sorry

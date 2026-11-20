-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerNegativeWeightedIntegralReflect
-- name    : Kyprianou.Ch01.stableAlphaPowerNegativeWeightedIntegralReflect
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:37:52.818678+00:00
-- url     : https://prove2.me/theorems/bcc25755-0980-46f9-8ca8-adf8a32de8e9
-- title:
--   Reflect original compensated stable power-law negative-halfline integral to positive radii
-- statement:
--   For any stable index alpha and coefficient c, the negative-halfline power-law weighted compensated Fourier integral exactly equals the positive-halfline power-law integral evaluated at opposite frequency. It preserves the original compensation cutoff and is an exact generalisation of the already-Proved alpha-one reflection theorem.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, negative-jump stable Levy measure.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLevyCompensatorReflection
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaPowerNegativeWeightedIntegralReflect (alpha c xi : ℝ) :
    (∫ r in Set.Iio (0 : ℝ),
      (c * |r| ^ (-alpha - 1)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-alpha - 1)) •
        ProbabilityTheory.levyCompensatedIntegrand (-xi) r ∂volume) := by sorry

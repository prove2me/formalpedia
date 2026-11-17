-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricMeasure_oneInfinitelyDivisible
-- name    : Kyprianou.Ch01.geometricMeasure_oneInfinitelyDivisible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:50:04.994204+00:00
-- url     : https://prove2.me/theorems/8ec657d6-8803-4d81-9ac0-f7172f6f8c1d
-- title:
--   Complete infinite divisibility of the boundary geometric law with certain success
-- statement:
--   At the boundary geometric parameter p=1, the canonical geometric distribution is exactly the count Dirac mass at zero, whose real embedding is the real Dirac zero law. The full LevyFoundations infinitely divisible law definition then follows from the separately Proved Dirac-zero n-fold convolution-root theorem. This completes the boundary case of Kyprianou (2006) Chapter 1 Exercise 1.2(i) and is an essential branch for the canonical theorem, leaving only the strict p<1 compound Poisson construction.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.2(i), solution printed p. 299; Proved Kyprianou.Ch01.diracZeroInfinitelyDivisibleLaw and geometricMeasure_one_eqDiracZero.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
open MeasureTheory ProbabilityTheory LevyFoundations
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricMeasure_oneInfinitelyDivisible :
    LevyFoundations.isInfinitelyDivisibleLaw
      ((ProbabilityTheory.geometricMeasure (1 : unitInterval.Elem)).map
        (fun k : ℕ => (k : ℝ))) := by
  sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch06_exponentialSurvivalFiniteAlmostSurely
-- name    : Kyprianou.Ch06.exponentialSurvivalFiniteAlmostSurely
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:39:42.505892+00:00
-- url     : https://prove2.me/theorems/838125cc-83cd-4f2e-88b1-803cd5fcf398
-- title:
--   Positive-rate exponential survival implies finite terminal time almost surely
-- statement:
--   For any random extended nonnegative terminal time T under a probability law, an exact exponential survival distribution P[t<T]=exp(-rate t) with strictly positive rate implies P[T=∞]=0. Proof by upper-bounding the infinite-time event with survival at integer times and sending the integer observation time to infinity; this gives the missing finite-arrival component of Kyprianou Lemma 6.18.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.exponentialSurvivalFiniteAlmostSurely
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (T : Omega → WithTop NNReal) (rate : Real)
    (hRate : 0 < rate)
    (hSurv : ∀ t : NNReal,
      P {omega | (t : WithTop NNReal) < T omega} =
        ENNReal.ofReal (Real.exp (-(rate * (t : Real))))) :
    P {omega | T omega = ⊤} = 0 := by sorry

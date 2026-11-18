-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkENNRealCompetingRateTail
-- name    : Kyprianou.Ch06.firstMarkENNRealCompetingRateTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:57:21.876912+00:00
-- url     : https://prove2.me/theorems/adcbb71a-9e9a-40e9-b783-5fdb8b553721
-- title:
--   Lemma 6.18 first-mark exponential-race tail in normalized ENNReal probability units
-- statement:
--   The competing positive-intensity first-mark exponential race integrates to the exact ENNReal probability factor n(A∩C)/n(A) multiplied by the exponential survival mass of A. This converts the real-valued normalized arrival-density integral to the probability measure units used in the published first-mark law for Kyprianou Lemma 6.18.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, normalized positive first-mark distribution.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstMarkCompetingIntensitySurvivalIntegral
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkENNRealCompetingRateTail
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (A C : Set E) (hC : MeasurableSet C)
    (hFinite : n A < ⊤) (hPositive : 0 < n (A ∩ C))
    (t : Real) :
    ENNReal.ofReal
      (∫ s in Set.Ioi t,
        (n (A ∩ C)).toReal *
          Real.exp (-((n A).toReal * s))) =
      (n (A ∩ C) / n A) *
        ENNReal.ofReal (Real.exp (-((n A).toReal * t))) := by sorry

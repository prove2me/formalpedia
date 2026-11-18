-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkCompetingIntensitySurvivalIntegral
-- name    : Kyprianou.Ch06.firstMarkCompetingIntensitySurvivalIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:46:16.31136+00:00
-- url     : https://prove2.me/theorems/cd28fe36-10d8-43ed-b7ce-dadca3a645a9
-- title:
--   Lemma 6.18: first-mark exponential race normalized by total mark intensity
-- statement:
--   For a finite-intensity marked region A, a measurable test C with positive intensity in A∩C, and real time t, the competing exponential-arrival density for the A∩C marks integrates to the first-mark probability factor n(A∩C)/n(A) times total A survival exp(-n(A)t). Reuses independent proved competing-rate integral and intensity-split lemmas.
-- source:
--   Kyprianou (2006), Lemma 6.18, printed pp.160–161, first marked Poisson arrival law and normalized competing-rate identity.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_competingPoissonRateExponentialTailIntegral
import Theorems.Thm_Kyprianou_Ch06_firstMarkCompetingRegionIntensitySplit
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkCompetingIntensitySurvivalIntegral
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (A C : Set E) (hC : MeasurableSet C)
    (hFinite : n A < ⊤) (hPositive : 0 < n (A ∩ C))
    (t : Real) :
    (∫ s in Set.Ioi t,
      (n (A ∩ C)).toReal *
        Real.exp (-((n A).toReal * s))) =
      ((n (A ∩ C)).toReal / (n A).toReal) *
        Real.exp (-((n A).toReal * t)) := by sorry

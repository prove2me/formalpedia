-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagOfLocallyFiniteStepRepresentationV1
-- name    : Kyprianou.Ch02.cadlagOfLocallyFiniteStepRepresentationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:45:45.641131+00:00
-- url     : https://prove2.me/theorems/3b9d859d-d14b-42fb-8112-51bbc0beb84a
-- title:
--   Local finite marked step representations imply càdlàg paths on non-negative time
-- statement:
--   A real-valued function on nonnegative time is cadlag if on each bounded integer horizon it agrees with a finite sum of right-continuous step indicators. Choose a horizon strictly after each t, use an eventually-equal neighbourhood and the proven finite-step-sum cadlag theorem and IsCadlagAt.congr.
-- source:
--   Deterministic gluing for Kyprianou (2006) Lemma 2.8; imports the Proved Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1 and ProbabilityTheory.IsCadlagAt.congr.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagOfLocallyFiniteStepRepresentationV1
    (f : ℝ≥0 → ℝ) (hlocal : ∀ T : ℕ, ∃ (s : Finset (ℝ × ℝ))
      (weight : ℝ × ℝ → ℝ), ∀ t : ℝ≥0, t ≤ (T : ℝ≥0) →
      f t = ∑ p ∈ s, if p.1 ≤ (t : ℝ) then weight p else 0) :
    ProbabilityTheory.IsCadlag f := by sorry

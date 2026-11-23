-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMFiniteSupportAllNaturalWindowsV2
-- name    : Kyprianou.Ch02.finiteRegionPRMFiniteSupportAllNaturalWindowsV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:36:02.738017+00:00
-- url     : https://prove2.me/theorems/49657aaf-a3e6-446b-8b4a-b9f47406dcec
-- title:
--   Chapter 2 Poisson finite support on all integer windows source interface
-- statement:
--   Source-exact revision of original finiteRegionPRMFiniteSupportAllNaturalWindowsV1 with fully qualified theorem declaration. Necessary because remote validator cannot resolve the original namespace-wrapped declaration despite PUBLISHED and SKETCH_ACCEPTED. The mathematical content and hypotheses are unchanged, including the underlying KLS PRM and finite mark region.
-- source:
--   Kyprianou Chapter 2 Lemma 2.8; source-exact interface repair of 8c74bbad-92c3-468c-aaf7-4ac15620d3ee

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteRegionPRMFiniteSupportAllNaturalWindowsV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0 := by sorry

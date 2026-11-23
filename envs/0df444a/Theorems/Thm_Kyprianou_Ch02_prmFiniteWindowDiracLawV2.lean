-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteWindowDiracLawV2
-- name    : Kyprianou.Ch02.prmFiniteWindowDiracLawV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:36:02.869808+00:00
-- url     : https://prove2.me/theorems/85c15bed-00ff-4d87-8784-ba53d6ac8706
-- title:
--   Chapter 2 exact finite-window Poisson Dirac law source interface
-- statement:
--   Source-exact revision of original prmFiniteWindowDiracLawV1 with fully qualified theorem declaration. Necessary because remote validator cannot resolve the original namespace-wrapped declaration despite PUBLISHED and SKETCH_ACCEPTED. The mathematical content and hypotheses are unchanged, including the underlying KLS PRM and finite mark region.
-- source:
--   Kyprianou Chapter 2 Lemma 2.8; source-exact interface repair of bcee54e1-d7b5-40f5-a6a0-0f58769ebcee

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteWindowDiracLawV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      (N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) =
        ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) {p} • Measure.dirac p := by sorry

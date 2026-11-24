-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramEmpty_fibre_eq_dirac_of_unique
-- name    : GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_eq_dirac_of_unique
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:44.877292+00:00
-- url     : https://prove2.me/theorems/ef48f541-3de8-4fef-aa88-54788cdc616f
-- title:
--   Gram Empty: fibre eq dirac of unique
-- statement:
--   The Gram Empty construction uses the fibre eq dirac of unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankZeroGramFiberMeasure.lean#L9-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankZeroGramFiberMeasure.lean#L9-L25

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankZeroGramFiberMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramEmpty

theorem GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_eq_dirac_of_unique {V X : Type} [MeasurableSpace V] [MeasurableSpace X] [Subsingleton V]
    [Subsingleton X] (μ : Measure V) (ν : Measure X) (m : X → Measure V) (x₀ : V)
    (hμ : μ Set.univ = 1) (hν : ν Set.univ = 1)
    (h : ∀ φ : V → ℝ≥0∞, Measurable φ → ∫⁻ v, φ v ∂μ = ∫⁻ b, ∫⁻ v, φ v ∂(m b) ∂ν) (S : X) :
    m S = Measure.dirac x₀ := by sorry

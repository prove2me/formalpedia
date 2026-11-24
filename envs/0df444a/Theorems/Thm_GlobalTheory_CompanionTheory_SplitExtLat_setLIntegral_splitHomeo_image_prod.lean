-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_setLIntegral_splitHomeo_image_prod
-- name    : GlobalTheory.CompanionTheory.SplitExtLat.setLIntegral_splitHomeo_image_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:14:59.561939+00:00
-- url     : https://prove2.me/theorems/4d4c4e78-27e3-46c9-8805-196b484af197
-- title:
--   Split Ext Lat: set LIntegral split Homeo image prod
-- statement:
--   The Split Ext Lat construction uses the set LIntegral split Homeo image prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLeviIntegralFormula.lean#L8-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLeviIntegralFormula.lean#L8-L42

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLeviIntegralFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitExtLat

theorem GlobalTheory.CompanionTheory.SplitExtLat.setLIntegral_splitHomeo_image_prod
    (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P]
    [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure]
    (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁) :
    MeasurableSet D → NullMeasurableSet 𝓕₁ μ₁ →
      NullMeasurableSet (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))
        (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) ∧
      ∀ f : P → ℝ≥0∞, Measurable f →
        ∫⁻ p in (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)), f p
            ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) =
          ∫⁻ u in 𝓕₁, ∫⁻ m in D, f ((m : P) * ι u) ∂ν ∂μ₁ := by sorry

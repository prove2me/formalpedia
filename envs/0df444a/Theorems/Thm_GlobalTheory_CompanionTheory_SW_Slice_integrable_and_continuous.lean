-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_integrable_and_continuous
-- name    : GlobalTheory.CompanionTheory.SW.Slice.integrable_and_continuous
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:52.896946+00:00
-- url     : https://prove2.me/theorems/cba0e429-0bde-4526-9ddb-5337ab3def88
-- title:
--   Slice: integrable and continuous
-- statement:
--   The Slice construction uses the integrable and continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L210-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L210-L260

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
variable {V X Q : Type} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
  [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]

theorem GlobalTheory.CompanionTheory.SW.Slice.integrable_and_continuous [T2Space V] {g : V → X} (hg : Continuous g) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) {w : Q → ℝ≥0} (hw : Continuous w)
    (m : Measure (g ⁻¹' {b₀})) [IsLocallyFiniteMeasure m] {φ : V → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    (∀ b ∈ Set.range (fun q : Q => q • b₀), Integrable φ (fibFam g b₀ w m b)) ∧
      ContinuousOn (fun b => ∫ v, φ v ∂(fibFam g b₀ w m b))
        (Set.range (fun q : Q => q • b₀)) := by sorry

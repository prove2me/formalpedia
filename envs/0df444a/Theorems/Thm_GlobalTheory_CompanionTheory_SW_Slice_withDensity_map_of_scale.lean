-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_withDensity_map_of_scale
-- name    : GlobalTheory.CompanionTheory.SW.Slice.withDensity_map_of_scale
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:57.123936+00:00
-- url     : https://prove2.me/theorems/35677022-f888-4aaf-84b9-13f1ed9e1e0c
-- title:
--   Slice: with Density map of scale
-- statement:
--   The Slice construction uses the with Density map of scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L31-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L31-L51

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

theorem GlobalTheory.CompanionTheory.SW.Slice.withDensity_map_of_scale {W : Type} [MeasurableSpace W] {L : W → W} (hL : Measurable L)
    (ρ : Measure W) (c k : ℝ≥0∞) (hρ : ρ.map L = c • ρ) {d : W → ℝ≥0∞} (hd : Measurable d)
    (hk : ∀ w, d w = k * d (L w)) (hck : k * c = 1) :
    (ρ.withDensity d).map L = ρ.withDensity d := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_comap_map_of_intertwine
-- name    : GlobalTheory.CompanionTheory.SW.Slice.comap_map_of_intertwine
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:36.457518+00:00
-- url     : https://prove2.me/theorems/a1b41bca-1606-4afd-8927-73f446d70d37
-- title:
--   Slice: comap map of intertwine
-- statement:
--   The Slice construction uses the comap map of intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L10-L29

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

theorem GlobalTheory.CompanionTheory.SW.Slice.comap_map_of_intertwine {W V : Type} [MeasurableSpace W] [MeasurableSpace V]
    {T : W → V} (hT : MeasurableEmbedding T) {L L' : W → W} {A A' : V → V}
    (hL : Measurable L) (hA : Measurable A) (hLL' : ∀ w, L (L' w) = w)
    (hAA' : ∀ v, A' (A v) = v)
    (hint : ∀ w, T (L w) = A (T w)) (hint' : ∀ w, T (L' w) = A' (T w))
    (μ : Measure V) (c : ℝ≥0∞) (hμ : μ.map A = c • μ) :
    (μ.comap T).map L = c • μ.comap T := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_comap_isLocallyFinite
-- name    : GlobalTheory.CompanionTheory.SW.Slice.comap_isLocallyFinite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:32.191276+00:00
-- url     : https://prove2.me/theorems/b698aeba-1ee1-40ab-9f22-4a7ed5b9f179
-- title:
--   Slice: comap is Locally Finite
-- statement:
--   The Slice construction uses the comap is Locally Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L53-L62

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

theorem GlobalTheory.CompanionTheory.SW.Slice.comap_isLocallyFinite {W V : Type} [TopologicalSpace W] [MeasurableSpace W]
    [TopologicalSpace V] [MeasurableSpace V] [BorelSpace W] [BorelSpace V] {T : W → V}
    (hT : IsOpenEmbedding T) (μ : Measure V) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.comap T) := by sorry

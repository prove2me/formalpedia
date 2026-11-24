-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarTransport_map_addEquiv_haar
-- name    : GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:06:55.280189+00:00
-- url     : https://prove2.me/theorems/7abbb9fe-1387-4d8c-b183-ec635f8941df
-- title:
--   Haar Transport: map add Equiv haar
-- statement:
--   The Haar Transport construction uses the map add Equiv haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarMeasureProdOfAddGroups.lean#L8-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarMeasureProdOfAddGroups.lean#L8-L41

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMeasureProdOfAddGroups
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarTransport

theorem GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [IsTopologicalAddGroup V] [AddCommGroup V'] [TopologicalSpace V'] [LocallyCompactSpace V']
    [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V']
    [IsTopologicalAddGroup V'] (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V')
    [μ'.IsAddHaarMeasure] (e : V ≃+ V') (he : Continuous e) (hes : Continuous e.symm) :
    (∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ') ∧
      ∀ (L : Set V) (L' : Set V'), IsCompact L → IsOpen L → L.Nonempty →
        (∀ v, e v ∈ L' ↔ v ∈ L) → μ L = μ' L' → μ.map e = μ' := by sorry

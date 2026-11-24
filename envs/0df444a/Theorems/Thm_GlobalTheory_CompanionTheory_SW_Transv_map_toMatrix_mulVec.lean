-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Transv_map_toMatrix_mulVec
-- name    : GlobalTheory.CompanionTheory.SW.Transv.map_toMatrix_mulVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:54.59335+00:00
-- url     : https://prove2.me/theorems/3d706d16-9d88-4795-94c9-0ba1ac7ee871
-- title:
--   Transv: map to Matrix mul Vec
-- statement:
--   The Transv construction uses the map to Matrix mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarInvariantUnderTransvection.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarInvariantUnderTransvection.lean#L64-L75

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvection
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Transv

theorem GlobalTheory.CompanionTheory.SW.Transv.map_toMatrix_mulVec (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K))
    [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K) :
    μ.map (fun x => t.toMatrix *ᵥ x) = μ := by sorry

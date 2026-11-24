-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Transv_measurePreserving_pi
-- name    : GlobalTheory.CompanionTheory.SW.Transv.measurePreserving_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:47.673338+00:00
-- url     : https://prove2.me/theorems/6309553b-dea1-4499-9f73-38c9ac87a360
-- title:
--   Transv: measure Preserving pi
-- statement:
--   The Transv construction uses the measure Preserving pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarInvariantUnderTransvection.lean#L22-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarInvariantUnderTransvection.lean#L22-L62

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

theorem GlobalTheory.CompanionTheory.SW.Transv.measurePreserving_pi {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Measure K) [SigmaFinite ν]
    [ν.IsAddLeftInvariant] (t : Matrix.TransvectionStruct ι K) :
    MeasurePreserving (fun x : ι → K => t.toMatrix *ᵥ x)
      (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by sorry

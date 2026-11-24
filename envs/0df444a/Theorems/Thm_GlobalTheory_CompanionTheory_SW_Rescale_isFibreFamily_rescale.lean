-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Rescale_isFibreFamily_rescale
-- name    : GlobalTheory.CompanionTheory.SW.Rescale.isFibreFamily_rescale
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:34.678948+00:00
-- url     : https://prove2.me/theorems/ee2e223c-5990-4e89-8d3d-e463cd42716b
-- title:
--   Rescale: is Fibre Family rescale
-- statement:
--   The Rescale construction uses the is Fibre Family rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FibreFamilySmul.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FibreFamilySmul.lean#L9-L26

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FibreFamilySmul
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Rescale

theorem GlobalTheory.CompanionTheory.SW.Rescale.isFibreFamily_rescale (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y)
    (ι : X → Y) (U : Set V) (B : Set X) (fib : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) (a c : ℝ≥0) (hc : c ≠ 0) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (a • μ) f ι U (c • ν) B (fun b => (a / c) • fib b) := by sorry

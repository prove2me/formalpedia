-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_measurable_open
-- name    : GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.measurable_open
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:03:50.035408+00:00
-- url     : https://prove2.me/theorems/a30635db-90eb-47aa-b707-505f869dece0
-- title:
--   Bump Family: measurable open
-- statement:
--   The Bump Family construction uses the measurable open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L97-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L97-L114

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreFam
variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.measurable_open [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {O : Set V} (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable fun b => fib b O := by sorry

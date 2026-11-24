-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_not_lt_of_setLIntegral_compact_eq
-- name    : GlobalTheory.CompanionTheory.SW.not_lt_of_setLIntegral_compact_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:12:34.008921+00:00
-- url     : https://prove2.me/theorems/fcebc7b0-e688-4e7f-b034-75963bb8eca9
-- title:
--   SW: not lt of set LIntegral compact eq
-- statement:
--   The SW construction uses the not lt of set LIntegral compact eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ContinuousDensitiesEqOfIntegralsOnCompacts.lean#L8-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ContinuousDensitiesEqOfIntegralsOnCompacts.lean#L8-L36

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompacts
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.not_lt_of_setLIntegral_compact_eq {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν]
    [ν.IsOpenPosMeasure] {B : Set X} (hB : IsOpen B) {D D' : X → ℝ≥0∞}
    (hD : ContinuousOn D B) (hD' : ContinuousOn D' B)
    (h : ∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν)
    {b : X} (hb : b ∈ B) : ¬ D b < D' b := by sorry

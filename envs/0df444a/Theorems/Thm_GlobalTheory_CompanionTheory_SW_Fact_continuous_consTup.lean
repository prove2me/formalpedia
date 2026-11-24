-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Fact_continuous_consTup
-- name    : GlobalTheory.CompanionTheory.SW.Fact.continuous_consTup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:03:46.025068+00:00
-- url     : https://prove2.me/theorems/4607a316-8437-4145-aef8-d4a88b05ecb0
-- title:
--   Fact: continuous cons Tup
-- statement:
--   The Fact construction uses the continuous cons Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryActionConsTupleMeasurable.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryActionConsTupleMeasurable.lean#L10-L17

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionConsTupleMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Fact

theorem GlobalTheory.CompanionTheory.SW.Fact.continuous_consTup {K : Type} [Zero K] [One K] [TopologicalSpace K] (n M : ℕ) :
    Continuous (fun X : Fin n → Fin M → K => (consTup X : Fin (n + 1) → Fin (M + 1) → K)) := by sorry

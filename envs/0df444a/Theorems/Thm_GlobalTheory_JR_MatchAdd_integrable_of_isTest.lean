-- Prove2me | Theorems.Thm_GlobalTheory_JR_MatchAdd_integrable_of_isTest
-- name    : GlobalTheory.JR.MatchAdd.integrable_of_isTest
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:35:24.08774+00:00
-- url     : https://prove2.me/theorems/1cd45308-35da-4093-953c-846ecd700081
-- title:
--   Match Add: integrable of is Test
-- statement:
--   The Match Add construction uses the integrable of is Test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisMatchingAdd.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisMatchingAdd.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisMatchingAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.MatchAdd.integrable_of_isTest {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : IsTest f) :
    Integrable f μ := by sorry

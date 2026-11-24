-- Prove2me | Theorems.Thm_GlobalTheory_JR_isTest_indicator_one_of_clopen_compact
-- name    : GlobalTheory.JR.isTest_indicator_one_of_clopen_compact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:38:23.7528+00:00
-- url     : https://prove2.me/theorems/0bf8259f-ba71-4a74-a0ec-9a306ac6310e
-- title:
--   JR: is Test indicator one of clopen compact
-- statement:
--   The JR construction uses the is Test indicator one of clopen compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsTestUnitIndicatorHermitianBlock.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsTestUnitIndicatorHermitianBlock.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsTestUnitIndicatorHermitianBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR

theorem GlobalTheory.JR.isTest_indicator_one_of_clopen_compact {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S)
    (hK : IsCompact S) : IsTest (Set.indicator S (1 : X → ℂ)) := by sorry

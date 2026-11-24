-- Prove2me | Theorems.Thm_GlobalTheory_isTest_nhds_inv
-- name    : GlobalTheory.isTest_nhds_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:14.325743+00:00
-- url     : https://prove2.me/theorems/670d7129-971a-4604-bae4-8bc010fe4e3b
-- title:
--   Global Theory: is Test nhds inv
-- statement:
--   The Global Theory construction uses the is Test nhds inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNhdsZeroTranslationInvariantOfLocallyConst.lean#L6-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNhdsZeroTranslationInvariantOfLocallyConst.lean#L6-L34

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsZeroTranslationInvariantOfLocallyConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.isTest_nhds_inv : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ),
    IsTest f → ∃ U ∈ 𝓝 (0 : X), ∀ x : X, ∀ u ∈ U, f (x + u) = f x := by sorry

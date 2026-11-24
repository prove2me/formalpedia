-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_nhds_zero_translation_invariant_of_locallyConstant
-- name    : GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:04.527885+00:00
-- url     : https://prove2.me/theorems/36e09cd4-b783-4581-bc07-c0ddce846e3e
-- title:
--   T: exists nhds zero translation invariant of locally Constant
-- statement:
--   The T construction uses the exists nhds zero translation invariant of locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNhdsZeroTranslationInvariantOfLocallyConstStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNhdsZeroTranslationInvariantOfLocallyConstStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsZeroTranslationInvariantOfLocallyConst
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsZeroTranslationInvariantOfLocallyConstStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ), IsTest f → ∃ U ∈ 𝓝 (0 : X), ∀ x : X, ∀ u ∈ U, f (x + u) = f x := by sorry

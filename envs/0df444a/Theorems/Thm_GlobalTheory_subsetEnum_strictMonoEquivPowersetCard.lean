-- Prove2me | Theorems.Thm_GlobalTheory_subsetEnum_strictMonoEquivPowersetCard
-- name    : GlobalTheory.subsetEnum_strictMonoEquivPowersetCard
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:29.7528+00:00
-- url     : https://prove2.me/theorems/a481535e-b9d1-4d5e-9c9e-83145c11dfb8
-- title:
--   Global Theory: subset Enum strict Mono Equiv Powerset Card
-- statement:
--   The Global Theory construction uses the subset Enum strict Mono Equiv Powerset Card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalMinorsMatrixMemUnitaryGroup.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalMinorsMatrixMemUnitaryGroup.lean#L17-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Classical
open GlobalTheory

theorem GlobalTheory.subsetEnum_strictMonoEquivPowersetCard (a : ℕ) {n : Type*} [LinearOrder n]
    (s : {s : Fin a → n // StrictMono s}) :
    subsetEnum (strictMonoEquivPowersetCard a n s) = s.1 := by sorry

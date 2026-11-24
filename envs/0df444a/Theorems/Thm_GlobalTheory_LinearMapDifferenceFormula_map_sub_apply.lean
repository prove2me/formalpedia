-- Prove2me | Theorems.Thm_GlobalTheory_LinearMapDifferenceFormula_map_sub_apply
-- name    : GlobalTheory.LinearMapDifferenceFormula.map_sub_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:10:49.483731+00:00
-- url     : https://prove2.me/theorems/124e9f34-b8e3-432c-b999-f2fc3f11d11d
-- title:
--   Linear Map Difference Formula: map sub apply
-- statement:
--   The Linear Map Difference Formula construction uses the map sub apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapSubApply.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapSubApply.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapSubApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LinearMapDifferenceFormula
open AdicCompletion

theorem GlobalTheory.LinearMapDifferenceFormula.map_sub_apply {A : Type} [CommRing A] (J : Ideal A) {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (h k : M →ₗ[A] P) (y : AdicCompletion J M) :
    AdicCompletion.map J (h - k) y = AdicCompletion.map J h y - AdicCompletion.map J k y := by sorry

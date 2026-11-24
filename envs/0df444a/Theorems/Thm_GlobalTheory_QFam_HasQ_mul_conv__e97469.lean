-- Prove2me | Theorems.Thm_GlobalTheory_QFam_HasQ_mul_conv__e97469
-- name    : GlobalTheory.QFam.HasQ.mul_conv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:00:05.204042+00:00
-- url     : https://prove2.me/theorems/e97469a5-0bd4-44d5-a511-b6c97aacbaa8
-- title:
--   Has Q: mul conv
-- statement:
--   The Has Q construction uses the mul conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelMulOfPosLevel.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelMulOfPosLevel.lean#L35-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.HasQ.mul_conv {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ * g τ) (conv a b) := by sorry

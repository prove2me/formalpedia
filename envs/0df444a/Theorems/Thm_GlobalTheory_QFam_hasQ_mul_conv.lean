-- Prove2me | Theorems.Thm_GlobalTheory_QFam_hasQ_mul_conv
-- name    : GlobalTheory.QFam.hasQ_mul_conv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:31.105024+00:00
-- url     : https://prove2.me/theorems/a520549e-40b2-4ee9-b5bc-b274dc2df904
-- title:
--   QFam: has Q mul conv
-- statement:
--   The QFam construction uses the has Q mul conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelMulOfPosLevel.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelMulOfPosLevel.lean#L39-L42

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

theorem GlobalTheory.QFam.hasQ_mul_conv : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b →
    HasQ N (fun τ => f τ * g τ) (conv a b) := by sorry

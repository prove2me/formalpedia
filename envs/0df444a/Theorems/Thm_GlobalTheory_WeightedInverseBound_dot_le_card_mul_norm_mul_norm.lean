-- Prove2me | Theorems.Thm_GlobalTheory_WeightedInverseBound_dot_le_card_mul_norm_mul_norm
-- name    : GlobalTheory.WeightedInverseBound.dot_le_card_mul_norm_mul_norm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:23.877125+00:00
-- url     : https://prove2.me/theorems/b57d8146-2eb9-43c8-b80f-a934def57749
-- title:
--   Weighted Inverse Bound: dot le card mul norm mul norm
-- statement:
--   The Weighted Inverse Bound construction uses the dot le card mul norm mul norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L38-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open GlobalTheory.WeightedInverseBound

theorem GlobalTheory.WeightedInverseBound.dot_le_card_mul_norm_mul_norm {g : ℕ} (x y : Fin g → ℝ) : x ⬝ᵥ y ≤ g * (‖x‖ * ‖y‖) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_PowerTwoNormLowerBound_norm_pow_two_pow_sub_one_ge
-- name    : GlobalTheory.PowerTwoNormLowerBound.norm_pow_two_pow_sub_one_ge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:54:03.578365+00:00
-- url     : https://prove2.me/theorems/1d005f50-8dc5-421d-82da-b0aebd7be751
-- title:
--   Power Two Norm Lower Bound: norm pow two pow sub one ge
-- statement:
--   The Power Two Norm Lower Bound construction uses the norm pow two pow sub one ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormPowTwoPowSubOneGe.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormPowTwoPowSubOneGe.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerTwoNormLowerBound

theorem GlobalTheory.PowerTwoNormLowerBound.norm_pow_two_pow_sub_one_ge {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < (1 / 2 : ℝ)) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by sorry

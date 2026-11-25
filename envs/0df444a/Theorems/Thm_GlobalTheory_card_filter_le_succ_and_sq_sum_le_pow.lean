-- Prove2me | Theorems.Thm_GlobalTheory_card_filter_le_succ_and_sq_sum_le_pow
-- name    : GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:34.191043+00:00
-- url     : https://prove2.me/theorems/f500974c-b93f-45ce-ba9d-9d24b8ac919e
-- title:
--   Global Theory: card filter le succ and sq sum le pow
-- statement:
--   The Global Theory construction uses the card filter le succ and sq sum le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CardFilterLeSuccAndSqSumLePow.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CardFilterLeSuccAndSqSumLePow.lean#L7-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterLeSuccAndSqSumLePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow : ∀ (n kk : ℕ) (bv : ℝ), 1 ≤ kk → kk + 1 ≤ n → (n : ℝ) ≤ bv → (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk ∧ (18 / 13 : ℝ) ^ 2 + ((n + 1 - kk : ℕ) : ℝ) * (3 * (6 * bv) ^ (n - kk)) ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) := by sorry

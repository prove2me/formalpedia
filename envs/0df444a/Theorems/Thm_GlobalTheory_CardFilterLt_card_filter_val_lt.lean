-- Prove2me | Theorems.Thm_GlobalTheory_CardFilterLt_card_filter_val_lt
-- name    : GlobalTheory.CardFilterLt.card_filter_val_lt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:03.214666+00:00
-- url     : https://prove2.me/theorems/eb37ff67-5cdd-4c76-be3e-4e6dbdd3f007
-- title:
--   Card Filter Lt: card filter val lt
-- statement:
--   The Card Filter Lt construction uses the card filter val lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardFilterValLt.lean#L5-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardFilterValLt.lean#L5-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardFilterValLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardFilterLt

theorem GlobalTheory.CardFilterLt.card_filter_val_lt : ∀ {n h : ℕ}, h ≤ n → Finset.card {m : Fin n | (↑m : ℕ) < h} = h := by sorry

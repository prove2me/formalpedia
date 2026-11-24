-- Prove2me | Theorems.Thm_GlobalTheory_card_quot_span_pow_succ_eq_mul_domain
-- name    : GlobalTheory.card_quot_span_pow_succ_eq_mul_domain
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:34.688432+00:00
-- url     : https://prove2.me/theorems/c83c47fa-8f21-4fd9-a171-848296b8b262
-- title:
--   Global Theory: card quot span pow succ eq mul domain
-- statement:
--   The Global Theory construction uses the card quot span pow succ eq mul domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardQuotSpanPowEqCardPowDomain.lean#L6-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardQuotSpanPowEqCardPowDomain.lean#L6-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotSpanPowEqCardPowDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.card_quot_span_pow_succ_eq_mul_domain (O : Type) [CommRing O] [IsDomain O] (t : O) (ht : t ≠ 0)
    (r : ℕ) :
    Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) =
      Nat.card (O ⧸ Ideal.span {t}) * Nat.card (O ⧸ Ideal.span {t ^ r}) := by sorry

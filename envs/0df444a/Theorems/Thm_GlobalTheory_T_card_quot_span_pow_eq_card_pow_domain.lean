-- Prove2me | Theorems.Thm_GlobalTheory_T_card_quot_span_pow_eq_card_pow_domain
-- name    : GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:28:11.614892+00:00
-- url     : https://prove2.me/theorems/bfd22652-acdf-415d-8084-b5337c39509e
-- title:
--   T: card quot span pow eq card pow domain
-- statement:
--   The T construction uses the card quot span pow eq card pow domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardQuotSpanPowEqCardPowDomainStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardQuotSpanPowEqCardPowDomainStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotSpanPowEqCardPowDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotSpanPowEqCardPowDomainStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain : ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) → ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by sorry

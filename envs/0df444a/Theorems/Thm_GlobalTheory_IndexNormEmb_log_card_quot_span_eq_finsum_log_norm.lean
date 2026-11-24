-- Prove2me | Theorems.Thm_GlobalTheory_IndexNormEmb_log_card_quot_span_eq_finsum_log_norm
-- name    : GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:29.103193+00:00
-- url     : https://prove2.me/theorems/79078b71-0f61-4901-a10c-80bed79b3f8e
-- title:
--   Index Norm Emb: log card quot span eq finsum log norm
-- statement:
--   The Index Norm Emb construction uses the log card quot span eq finsum log norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardQuotSpanEqFinsumLogNormEmbeddings.lean#L49-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardQuotSpanEqFinsumLogNormEmbeddings.lean#L49-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardQuotSpanEqFinsumLogNormEmbeddings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.IndexNormEmb

theorem GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B),
    b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧
      Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by sorry

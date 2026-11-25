-- Prove2me | Theorems.Thm_GlobalTheory_T_log_card_quot_span_eq_finsum_log_norm_embeddings
-- name    : GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:12.517824+00:00
-- url     : https://prove2.me/theorems/5cf320d8-4501-57cf-bb3a-0d6cb4515a0f
-- title:
--   T: log card quot span eq finsum log norm embeddings
-- statement:
--   The T construction uses the log card quot span eq finsum log norm embeddings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardQuotSpanEqFinsumLogNormEmbeddingsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardQuotSpanEqFinsumLogNormEmbeddingsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardQuotSpanEqFinsumLogNormEmbeddings
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardQuotSpanEqFinsumLogNormEmbeddingsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B), b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧ Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by sorry

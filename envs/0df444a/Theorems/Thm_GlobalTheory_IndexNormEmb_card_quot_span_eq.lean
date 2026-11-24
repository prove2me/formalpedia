-- Prove2me | Theorems.Thm_GlobalTheory_IndexNormEmb_card_quot_span_eq
-- name    : GlobalTheory.IndexNormEmb.card_quot_span_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:20.521031+00:00
-- url     : https://prove2.me/theorems/40119c73-075c-4c33-90d6-38fa80014407
-- title:
--   Index Norm Emb: card quot span eq
-- statement:
--   The Index Norm Emb construction uses the card quot span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardQuotSpanEqFinsumLogNormEmbeddings.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardQuotSpanEqFinsumLogNormEmbeddings.lean#L9-L22

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

theorem GlobalTheory.IndexNormEmb.card_quot_span_eq (B : Type) [CommRing B] [IsDomain B] [Module.Free ℤ B] [Module.Finite ℤ B]
    (b : B) (hb : b ≠ 0) : Nat.card (B ⧸ Ideal.span {b}) = (Algebra.norm ℤ b).natAbs := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_RegularQuotient_quotient_span_range
-- name    : GlobalTheory.RegularQuotient.quotient_span_range
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:40.101967+00:00
-- url     : https://prove2.me/theorems/e9829bf9-10ea-542f-b4eb-2cb6ceb99008
-- title:
--   Regular Quotient: quotient span range
-- statement:
--   The Regular Quotient construction uses the quotient span range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuotientSpanRange.lean#L135-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuotientSpanRange.lean#L135-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuotientSpanRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Matrix
open GlobalTheory GlobalTheory.RegularQuotient
open IsLocalRing Matrix

theorem GlobalTheory.RegularQuotient.quotient_span_range : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (d k : ℕ)
    (x : Fin k → A),
    ringKrullDim A = ((d + k : ℕ) : WithBot ℕ∞) → (∀ i, x i ∈ maximalIdeal A) →
    (∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) →
    IsRegularLocalRing (A ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (A ⧸ Ideal.span (Set.range x)) = (d : WithBot ℕ∞) := by sorry

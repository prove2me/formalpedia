-- Prove2me | Theorems.Thm_GlobalTheory_RegularQuotient_quot_regular
-- name    : GlobalTheory.RegularQuotient.quot_regular
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:00.742246+00:00
-- url     : https://prove2.me/theorems/ad06d0e4-318b-4204-ae21-bda8f0ae37a1
-- title:
--   Regular Quotient: quot regular
-- statement:
--   The Regular Quotient construction uses the quot regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuotientSpanRange.lean#L9-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuotientSpanRange.lean#L9-L68

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

theorem GlobalTheory.RegularQuotient.quot_regular (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι κ : Type} [Fintype ι]
    [Fintype κ] (t : ι → Λ) (z : κ → Λ)
    (hs : Ideal.span (Set.range t ∪ Set.range z) = maximalIdeal Λ)
    (hd : ringKrullDim Λ = ((Fintype.card ι + Fintype.card κ : ℕ) : ℕ)) :
    ∃ _ : IsRegularLocalRing (Λ ⧸ Ideal.span (Set.range z)),
      Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range z))) (maximalIdeal Λ) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (Ideal.span (Set.range z)) (t i)) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      ringKrullDim (Λ ⧸ Ideal.span (Set.range z)) = (Fintype.card ι : ℕ) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_ValBoundDenom_exists_common_denominator_of_valuation_le
-- name    : GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:50:14.550022+00:00
-- url     : https://prove2.me/theorems/e39237c2-1fca-4125-a14d-be557be0b097
-- title:
--   Val Bound Denom: exists common denominator of valuation le
-- statement:
--   The Val Bound Denom construction uses the exists common denominator of valuation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCommonDenominatorOfValuationLeCofinite.lean#L15-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCommonDenominatorOfValuationLeCofinite.lean#L15-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCommonDenominatorOfValuationLeCofinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.ValBoundDenom

theorem GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le (E : Type) [Field E] [NumberField E]
    (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ))
    (hβ : ∀ᶠ w in Filter.cofinite, β w ≤ 1) : ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) →
        IsIntegral ℤ ((D : E) * x) := by sorry

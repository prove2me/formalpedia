-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_common_denominator_of_valuation_le_cofinite
-- name    : GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:33:49.705287+00:00
-- url     : https://prove2.me/theorems/7950353c-1f8c-4bf9-9f9f-af3227273017
-- title:
--   T: exists common denominator of valuation le cofinite
-- statement:
--   The T construction uses the exists common denominator of valuation le cofinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCommonDenominatorOfValuationLeCofiniteStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCommonDenominatorOfValuationLeCofiniteStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCommonDenominatorOfValuationLeCofinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCommonDenominatorOfValuationLeCofiniteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite : ∀ (E : Type) [Field E] [NumberField E] (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)),
    (∀ᶠ w in Filter.cofinite, β w ≤ 1) → ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) → IsIntegral ℤ ((D : E) * x) := by sorry

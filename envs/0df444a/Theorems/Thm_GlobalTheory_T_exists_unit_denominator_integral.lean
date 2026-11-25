-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unit_denominator_integral
-- name    : GlobalTheory.T.exists_unit_denominator_integral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:03.274108+00:00
-- url     : https://prove2.me/theorems/c9594599-d42d-4d9a-a593-4697b9e094ff
-- title:
--   T: exists unit denominator integral
-- statement:
--   The T construction uses the exists unit denominator integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitDenominatorIntegralStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitDenominatorIntegralStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitDenominatorIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitDenominatorIntegralStatement
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

theorem GlobalTheory.T.exists_unit_denominator_integral : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (T : Set K) (d : 𝓞 K), d ≠ 0 → (∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) → (∀ t ∈ T, P.valuation K t ≤ 1) → ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) := by sorry

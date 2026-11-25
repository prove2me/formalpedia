-- Prove2me | Theorems.Thm_GlobalTheory_T_length_sum_height_one_disjoint_divisors
-- name    : GlobalTheory.T.length_sum_height_one_disjoint_divisors
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:26.48165+00:00
-- url     : https://prove2.me/theorems/31246a6a-a890-4b4e-b4a8-18f7a4830916
-- title:
--   T: length sum height one disjoint divisors
-- statement:
--   The T construction uses the length sum height one disjoint divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisorsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisorsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.length_sum_height_one_disjoint_divisors : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A], ringKrullDim A = 2 → ∀ (a b : A), a ≠ 0 → b ≠ 0 → ∀ (P Q : Finset (PrimeSpectrum A)), (∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) → (∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) → Disjoint P Q → ∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal b})).toNat = ∑ p ∈ Q, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) b})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal a})).toNat := by sorry

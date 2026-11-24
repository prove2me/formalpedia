-- Prove2me | Theorems.Thm_GlobalTheory_T_pow_prime_range_eq_iterated_difference
-- name    : GlobalTheory.T.pow_prime_range_eq_iterated_difference
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:55:07.421997+00:00
-- url     : https://prove2.me/theorems/ecb2a753-bc12-4c69-a827-4473d2ebd773
-- title:
--   T: pow prime range eq iterated difference
-- statement:
--   The T construction uses the pow prime range eq iterated difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowPrimeRangeEqIteratedDifferenceStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowPrimeRangeEqIteratedDifferenceStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifference
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifferenceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pow_prime_range_eq_iterated_difference : ∀ (p : ℕ) (M : Type) [CommGroup M] (τ : M →* M) (lam : Monoid.End M), p.Prime → (∀ a, lam a = τ a / a) → (∀ a, nrm τ p a = 1) → pows p (⊤ : Subgroup M) = MonoidHom.range (lam ^ (p - 1) : Monoid.End M) ∧ ∀ a : M, a ^ p = 1 ↔ (lam ^ (p - 1) : Monoid.End M) a = 1 := by sorry

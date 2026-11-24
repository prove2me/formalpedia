-- Prove2me | Theorems.Thm_GlobalTheory_T_card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank
-- name    : GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:56.56921+00:00
-- url     : https://prove2.me/theorems/0f84bfa9-968e-4915-ad86-550bdd4d0026
-- title:
--   T: card quot range prime smul eq card ker mul pow finrank
-- statement:
--   The T construction uses the card quot range prime smul eq card ker mul pow finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardQuotPrimeSmulEqCardKerMulPowFinrankStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardQuotPrimeSmulEqCardKerMulPowFinrankStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardQuotPrimeSmulEqCardKerMulPowFinrank
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardQuotPrimeSmulEqCardKerMulPowFinrankStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime], Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) = Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) * p ^ Module.finrank ℤ M := by sorry

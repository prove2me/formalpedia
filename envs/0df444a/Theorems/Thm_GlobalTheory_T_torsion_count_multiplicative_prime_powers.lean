-- Prove2me | Theorems.Thm_GlobalTheory_T_torsion_count_multiplicative_prime_powers
-- name    : GlobalTheory.T.torsion_count_multiplicative_prime_powers
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:39:48.29305+00:00
-- url     : https://prove2.me/theorems/1583abc8-6a5b-5982-874e-3e63be2307f8
-- title:
--   T: torsion count multiplicative prime powers
-- statement:
--   The T construction uses the torsion count multiplicative prime powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCountMultiplicativePrimePowersStatement.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCountMultiplicativePrimePowersStatement.lean#L6-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowersStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.torsion_count_multiplicative_prime_powers : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0}) →
    (∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    ∃ e : ℕ, 1 ≤ e ∧ ∀ j : ℕ, Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * (j + 1)), a • x = 0} =
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * j), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ e, a • x = 0} := by sorry

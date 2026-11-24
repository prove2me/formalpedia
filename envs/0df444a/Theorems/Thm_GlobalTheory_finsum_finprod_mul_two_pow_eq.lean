-- Prove2me | Theorems.Thm_GlobalTheory_finsum_finprod_mul_two_pow_eq
-- name    : GlobalTheory.finsum_finprod_mul_two_pow_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:00.670564+00:00
-- url     : https://prove2.me/theorems/8de99f68-13b5-4748-8d72-e1f5d3d89ced
-- title:
--   Global Theory: finsum finprod mul two pow eq
-- statement:
--   The Global Theory construction uses the finsum finprod mul two pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCount.lean#L174-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCount.lean#L174-L204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory
open Function

theorem GlobalTheory.finsum_finprod_mul_two_pow_eq :
    ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R)
      (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) →
      (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) →
      (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) →
      (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) →
        Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) →
      (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k =
        (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by sorry

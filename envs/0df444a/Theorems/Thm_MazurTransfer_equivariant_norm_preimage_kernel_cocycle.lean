-- Prove2me | Theorems.Thm_MazurTransfer_equivariant_norm_preimage_kernel_cocycle
-- name    : MazurTransfer.equivariant_norm_preimage_kernel_cocycle
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T19:09:21.545498+00:00
-- url     : https://prove2.me/theorems/e15e0cf0-d9f5-4212-91d2-ed59a1ab3d49
-- title:
--   Equivariant norm preimages give kernel cocycles independent of the lift
-- statement:
--   A surjective equivariant endomorphism of an abelian group with a group action sends the differences of a preimage of an invariant point into its kernel. These differences form a normalized cocycle. Changing the preimage changes the cocycle by a coboundary coming from the kernel. No continuity or fixed-point descent is asserted.
-- source:
--   Owned MazurTheorem algebraic Kummer argument, Apache-2.0, checked with Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474. Named consumer: both actual order-thirteen Picard norm maps, with field-automorphism action and geometric preimages established using pinned Anthropic FLT.

import Mathlib
universe u v

theorem MazurTransfer.equivariant_norm_preimage_kernel_cocycle
    (G : Type u) (H : Type v) [Group G] [CommGroup H]
    (ρ : G → H →* H) (f : H →* H)
    (hone : ∀ x, ρ 1 x = x)
    (hmul : ∀ σ τ x, ρ (σ * τ) x = ρ σ (ρ τ x))
    (heq : ∀ σ x, f (ρ σ x) = ρ σ (f x))
    (hsurj : Function.Surjective f) (a : H) (ha : ∀ σ, ρ σ a = a) :
    ∃ b : H, f b = a ∧
      (∀ σ, f (ρ σ b * b⁻¹) = 1) ∧
      (∀ σ τ, ρ (σ * τ) b * b⁻¹ = (ρ σ b * b⁻¹) * ρ σ (ρ τ b * b⁻¹)) ∧
      ρ 1 b * b⁻¹ = 1 ∧
      (∀ b' : H, f b' = a → f (b' * b⁻¹) = 1 ∧
        ∀ σ, ρ σ b' * b'⁻¹ = ρ σ (b' * b⁻¹) * (ρ σ b * b⁻¹) * (b' * b⁻¹)⁻¹) := by sorry

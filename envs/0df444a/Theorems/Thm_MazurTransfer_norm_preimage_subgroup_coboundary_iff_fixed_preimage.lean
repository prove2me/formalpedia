-- Prove2me | Theorems.Thm_MazurTransfer_norm_preimage_subgroup_coboundary_iff_fixed_preimage
-- name    : MazurTransfer.norm_preimage_subgroup_coboundary_iff_fixed_preimage
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T20:06:33.835182+00:00
-- url     : https://prove2.me/theorems/1d7d0ce9-ea95-4631-a3cc-fc6d40bac333
-- title:
--   Subgroup-trivial norm preimage cocycles have fixed preimages
-- statement:
--   Let G be a group, A an abelian group, and let ρ assign an endomorphism of A to each element of G. Let φ be an endomorphism of A, let S be a subgroup of G, and suppose φ(b)=a. The preimage differences ρ(σ)(b)/b on S are a coboundary with a witness in the kernel of φ if and only if a has a preimage c under φ fixed by every ρ(σ) for σ in S. No compatibility beyond the stated endomorphism hypotheses is needed.
--
--   This supplies the fixed-preimage interpretation of zero restricted Kummer classes, and is used for the actual rational Picard norm morphisms.
-- source:
--   Owned MazurTheorem norm descent argument, Apache-2.0. Checked source NormCocycleInvariantPreimageCriterion.coboundary_iff_invariant_preimage at Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474. Named downstream consumer: continuous actual norm class restrictions and decomposition-group local conditions.

import Mathlib

theorem MazurTransfer.norm_preimage_subgroup_coboundary_iff_fixed_preimage
    (G A : Type) [Group G] [CommGroup A] (ρ : G → A →* A) (φ : A →* A)
    (S : Subgroup G) (a b : A) (hb : φ b = a) :
    (∃ z : φ.ker, ∀ σ : S, ρ σ.val z.val * z.val⁻¹ = ρ σ.val b * b⁻¹) ↔
      ∃ c : A, φ c = a ∧ ∀ σ : S, ρ σ.val c = c := by sorry

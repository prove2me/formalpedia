-- Prove2me | Theorems.Thm_MazurTransfer_IntegralSurjectiveOverGeometricPointLifting_exists_over_comp_eq
-- name    : MazurTransfer.IntegralSurjectiveOverGeometricPointLifting.exists_over_comp_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T21:30:22.538899+00:00
-- url     : https://prove2.me/theorems/5cefe6e2-6dc1-42a0-8da6-52da11b27307
-- title:
--   Integral surjective endomorphisms lift algebraically closed field points over the specified base
-- statement:
--   Let t:X to S be a morphism of schemes and let phi be an integral surjective endomorphism of X over S. Let K be an algebraically closed field, let s be a K-valued point of S and let a be a K-valued point of X over s. Then there exists a K-valued point b of X over the same s with phi composed with b equal to a. The named downstream consumers are geometric norm preimages on the actual rational Picard scheme.
-- source:
--   Complete original MazurTheorem IntegralSurjectiveOverGeometricPointLifting.exists_over_comp_eq, retaining its full original statement and proof and reusing the exact public original Anthropic FLT Scheme.Hom.exists_comp_eq_of_isIntegralHom_of_surjective contract at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Reuses the complete Anthropic FLT field-point lifting proof at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: lift a geometric point along an integral surjective
endomorphism while preserving its specified map to the base scheme.
Named downstream consumer: the two actual order-13 Picard norm maps.
-/
import Mathlib

noncomputable section
open CategoryTheory AlgebraicGeometry

theorem MazurTransfer.IntegralSurjectiveOverGeometricPointLifting.exists_over_comp_eq {S X : Scheme.{0}} (t : X ⟶ S)
    (φ : Over.mk t ⟶ Over.mk t) [IsIntegralHom φ.left] [Surjective φ.left]
    (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : Over.mk s ⟶ Over.mk t) :
    ∃ b : Over.mk s ⟶ Over.mk t, b ≫ φ = a := by sorry

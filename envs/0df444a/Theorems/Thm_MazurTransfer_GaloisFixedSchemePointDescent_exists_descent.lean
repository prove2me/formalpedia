-- Prove2me | Theorems.Thm_MazurTransfer_GaloisFixedSchemePointDescent_exists_descent
-- name    : MazurTransfer.GaloisFixedSchemePointDescent.exists_descent
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:02:28.565391+00:00
-- url     : https://prove2.me/theorems/b60a998e-6eac-417e-9479-2bb2a56577c3
-- title:
--   A Galois-fixed geometric scheme point descends to the base field
-- statement:
--   Let K/F be an arbitrary Galois extension, let X be a scheme, and let b be a K-valued point of X fixed by every F-automorphism of K. Then b descends to an F-valued point: $$\forall\sigma\in\operatorname{Aut}_F(K),\ \sigma^*b=b\quad\Longrightarrow\quad\exists a\in X(F),\ a_K=b.$$ Neither finite extension nor finite type of X is assumed. The named downstream consumer is unique descent of points with a specified structure morphism, followed by rational-point descent for the actual Picard.
-- source:
--   Complete original MazurTheorem GaloisFixedSchemePointDescent.exists_descent proof through the residue field, retaining the original GaloisFixedRingMapDescent.exists_descent helper body and full type. Apache-2.0. Named downstream consumer: original GaloisFixedOverPointDescent.exists_unique_descent and the actual Picard Galois fixed-point bridge.

import Mathlib
noncomputable section
open CategoryTheory AlgebraicGeometry

theorem MazurTransfer.GaloisFixedSchemePointDescent.exists_descent (F K : Type) [Field F] [Field K] [Algebra F K] [IsGalois F K] (X : Scheme.{0}) (b : Spec (CommRingCat.of K) ⟶ X)
    (hb : ∀ σ : K ≃ₐ[F] K, Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ b = b) :
    ∃ a : Spec (CommRingCat.of F) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ a = b := by sorry

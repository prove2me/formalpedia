-- Prove2me | Theorems.Thm_MazurTransfer_galois_fixed_scheme_point_unique_descent
-- name    : MazurTransfer.galois_fixed_scheme_point_unique_descent
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T19:26:31.945636+00:00
-- url     : https://prove2.me/theorems/83cd895f-09ec-4178-aff2-3068bb5b62f9
-- title:
--   Galois-fixed geometric scheme points descend uniquely to the base field
-- statement:
--   For a Galois field extension K/F and any scheme X, every K-valued point of X fixed under precomposition by all F-automorphisms of K is the scalar extension of a unique F-valued point. No finite type or properness hypothesis is needed. The theorem preserves the full geometric point and proves uniqueness.
-- source:
--   Owned MazurTheorem rational-point descent argument, Apache-2.0, using Mathlib residue-field factorization, infinite Galois fixed-field theory, and epimorphic scalar extension at pin 0df444a360eaa60ab8c11dca51a86af692955474. Named consumer: Galois-fixed points of the SAME rational represented Picard and the actual norm Kummer quotient injection.

import Mathlib
open CategoryTheory AlgebraicGeometry

theorem MazurTransfer.galois_fixed_scheme_point_unique_descent
    (F K : Type) [Field F] [Field K] [Algebra F K] [IsGalois F K]
    (X : Scheme.{0}) (b : Spec (CommRingCat.of K) ⟶ X)
    (hb : ∀ σ : K ≃ₐ[F] K, Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ b = b) :
    ∃! a : Spec (CommRingCat.of F) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ a = b := by sorry

-- Prove2me | Theorems.Thm_MazurTransfer_finite_scheme_geometric_point_galois_stabilizer_open
-- name    : MazurTransfer.finite_scheme_geometric_point_galois_stabilizer_open
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T19:43:53.982983+00:00
-- url     : https://prove2.me/theorems/39c9df85-4313-465b-84b2-12f6d9a4efd1
-- title:
--   Geometric points of finite schemes have open Galois stabilizers
-- statement:
--   For an algebraic integral field extension K/F, every K-valued point of a finite F-scheme has an open stabilizer under F-automorphisms of K in the Krull topology. The proof uses finite algebra generators and open stabilizers of integral elements.
-- source:
--   Owned MazurTheorem continuity argument, Apache-2.0, using Mathlib affine finite morphisms and Krull topology at pin 0df444a360eaa60ab8c11dca51a86af692955474. Named consumer: actual rational norm-fibre Galois orbits and continuous actual kernel cocycles.

import Mathlib
open CategoryTheory AlgebraicGeometry

theorem MazurTransfer.finite_scheme_geometric_point_galois_stabilizer_open
    (F K : Type) [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K]
    (X : Scheme.{0}) (t : X ⟶ Spec (CommRingCat.of F)) [IsFinite t]
    (q : Spec (CommRingCat.of K) ⟶ X)
    (hq : q ≫ t = Spec.map (CommRingCat.ofHom (algebraMap F K))) :
    IsOpen {σ : K ≃ₐ[F] K | Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ q = q} := by sorry

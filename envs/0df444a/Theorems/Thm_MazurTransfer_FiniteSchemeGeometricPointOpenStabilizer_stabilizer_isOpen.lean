-- Prove2me | Theorems.Thm_MazurTransfer_FiniteSchemeGeometricPointOpenStabilizer_stabilizer_isOpen
-- name    : MazurTransfer.FiniteSchemeGeometricPointOpenStabilizer.stabilizer_isOpen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T23:19:29.541073+00:00
-- url     : https://prove2.me/theorems/ef87c739-7810-43d3-8564-73e83d716337
-- title:
--   Points of finite schemes over a field have open automorphism stabilizers
-- statement:
--   Let F be a field, K an algebraic field extension of F, and X a finite F-scheme. For a K-valued point q of X over F, its stabilizer $$\{\sigma\in\operatorname{Aut}_F(K):q\circ\operatorname{Spec}(\sigma)=q\}$$ is open for the Krull topology. This supplies the open stabilizers of points in finite rational norm fibres. No Galois or algebraic-closure assumption is added.
-- source:
--   Original MazurTheorem FiniteSchemeGeometricPointOpenStabilizer.stabilizer_isOpen; original proof retained, using the publicly checked finite-type algebra point stabilizer. Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a point of a scheme finite over a field has an open
Galois stabilizer in an algebraic extension, using finite affine
coordinates. Named downstream consumer: actual norm fibres and kernels.
-/
import Theorems.Thm_MazurTransfer_FiniteTypeGaloisAlgHomOpenStabilizer_stabilizer_isOpen
noncomputable section
open CategoryTheory AlgebraicGeometry

theorem MazurTransfer.FiniteSchemeGeometricPointOpenStabilizer.stabilizer_isOpen (F K : Type) [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K] (X : Scheme.{0}) (t : X ⟶ Spec (CommRingCat.of F)) [IsFinite t]
    (q : Spec (CommRingCat.of K) ⟶ X)
    (hq : q ≫ t = Spec.map (CommRingCat.ofHom (algebraMap F K))) :
    IsOpen {σ : K ≃ₐ[F] K | Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ q = q} := by sorry

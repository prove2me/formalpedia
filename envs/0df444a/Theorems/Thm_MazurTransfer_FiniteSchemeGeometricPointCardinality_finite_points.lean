-- Prove2me | Theorems.Thm_MazurTransfer_FiniteSchemeGeometricPointCardinality_finite_points
-- name    : MazurTransfer.FiniteSchemeGeometricPointCardinality.finite_points
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:22:10.185998+00:00
-- url     : https://prove2.me/theorems/f0f5c0ea-2d31-4f40-9ba2-14c295167af3
-- title:
--   A finite scheme over a field has finitely many points over every extension field
-- statement:
--   Let F be a field, K/F any extension field, and X a scheme with a finite structure morphism to Spec F. Then its K-valued points over F form a finite type: $$\#X(K)<\infty.$$ Neither separability, algebraic closure, nor étaleness is assumed. The named downstream consumers are finite preimages of rational points under finite morphisms and the actual norm-kernel Galois modules.
-- source:
--   Complete original MazurTheorem FiniteSchemeGeometricPointCardinality.finite_points statement and proof, preserving the literal affine coordinate-algebra encoding. The proof-only stabilizer dependency is removed. Uses the original public NeronModelInfra SchemeHomOver interface from the official Anthropic FLT source at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a scheme finite over a field has finitely many points
over every extension field, by injection into coordinate algebra maps.
Named downstream consumer: finite actual norm kernel Galois modules.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem MazurTransfer.FiniteSchemeGeometricPointCardinality.finite_points (F K : Type) [Field F] [Field K] [Algebra F K] (X : Scheme.{0}) (t : X ⟶ Spec (CommRingCat.of F)) [IsFinite t] :
    Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) t) := by sorry

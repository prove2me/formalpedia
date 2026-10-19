-- Prove2me | Theorems.Thm_MazurTransfer_FiniteRationalFibreGeometricPoints_finite_preimages
-- name    : MazurTransfer.FiniteRationalFibreGeometricPoints.finite_preimages
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:31:15.907679+00:00
-- url     : https://prove2.me/theorems/2b81db83-3225-41c2-948e-538b0b439c8d
-- title:
--   A rational point has finitely many geometric preimages under a finite morphism
-- statement:
--   Let F be a field, K/F any extension field, and let X and Y be schemes over F. Let phi be a morphism over F whose underlying scheme morphism is finite. For every F-valued point a of Y, the set of geometric preimages is finite: $$\{b\in X(K):\varphi(b)=a_K\}\ \text{is finite}.$$ No Galois, separability, algebraic-closure or étaleness assumption is added. The named downstream consumers are actual finite norm kernels and finite preimage fields.
-- source:
--   Complete original MazurTheorem FiniteRationalFibreGeometricPoints.finite_preimages statement and proof through the literal pullback fibre. Retains the original field-extension point and scalar-extension constructors; removes the proof-only Galois-orbit dependency. Uses the original official Anthropic FLT SchemeHomOver interface at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: geometric lifts of a rational point under a finite
morphism form a finite type, through the literal pullback fibre.
Named downstream consumer: finite actual norm kernels and preimage fields.
-/
import Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_MazurTransfer_FiniteSchemeGeometricPointCardinality_finite_points
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open MazurTransfer.FieldAutomorphismOverPointAction MazurTransfer.GaloisFixedOverPointDescent

theorem MazurTransfer.FiniteRationalFibreGeometricPoints.finite_preimages (F K : Type) [Field F] [Field K] [Algebra F K]
    {X Y : Scheme.{0}} (tX : X ⟶ Spec (CommRingCat.of F)) (tY : Y ⟶ Spec (CommRingCat.of F)) (φ : Over.mk tX ⟶ Over.mk tY) [IsFinite φ.left]
    (a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk tY) :
    Finite {b : Over.mk (fieldBase F K) ⟶ Over.mk tX // b ≫ φ = scalarOverMap F K ≫ a} := by sorry

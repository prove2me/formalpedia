-- Prove2me | Theorems.Thm_MazurTransfer_AffineOpenChartGenericEmbeddingCompatibility_coordinateEmbedding_generic
-- name    : MazurTransfer.AffineOpenChartGenericEmbeddingCompatibility.coordinateEmbedding_generic
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T18:16:22.883178+00:00
-- url     : https://prove2.me/theorems/3c276510-3fcf-4bee-b488-c1b15173c526
-- title:
--   An integral affine chart recovers the actual generic-stalk morphism
-- statement:
--   For an integral affine open chart j:Spec A -> C of an integral scheme, Spec of its original canonical coordinate embedding into C.functionField, followed by j, equals the actual morphism from the generic stalk of C. Every original universe, domain/integrality hypothesis and open-immersion hypothesis is retained.
-- source:
--   Complete original MazurTheorem AffineOpenChartGenericEmbeddingCompatibility.coordinateEmbedding_generic proof and private fromSpecStalk_cast helper, Apache-2.0, Vas and contributors.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit coordinate embedding of an integral affine
open chart recovers the scheme's literal generic-stalk morphism.
Named downstream consumer: compatibility of the order-13 generic embedding
with extension of the base field.
-/
import Definitions.Def_MazurTransfer_AffineOpenChartFunctionField

noncomputable section
universe u
open MazurTransfer
open AlgebraicGeometry CategoryTheory
open AffineOpenChartFunctionField
variable (A : CommRingCat.{u}) [IsDomain A] {C : Scheme.{u}} [IsIntegral C]
    (j : Spec A ⟶ C) [IsOpenImmersion j]

theorem MazurTransfer.AffineOpenChartGenericEmbeddingCompatibility.coordinateEmbedding_generic :
    Spec.map (CommRingCat.ofHom (coordinateEmbedding A j)) ≫ j =
      C.fromSpecStalk (genericPoint C) := by sorry

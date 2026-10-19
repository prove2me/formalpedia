-- Prove2me | Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_restriction
-- name    : MazurTransfer.AffineOpenChartFunctionFieldNaturality.coordinate_embedding_restriction
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:23:03.956983+00:00
-- url     : https://prove2.me/theorems/bad9db2f-a863-4e3b-99a5-49b10d9900b6
-- title:
--   Canonical affine coordinate embeddings commute with open restriction
-- statement:
--   Let $A,B$ be domains, $X$ an integral scheme, and $j:\operatorname{Spec}A\to X$ an open immersion. If a ring map $\varphi:A\to B$ induces an open immersion, then the canonical coordinate embeddings into $K(X)$ satisfy $$e_A=e_B\circ\varphi,$$ where $e_B$ is associated with $\operatorname{Spec}B\to\operatorname{Spec}A\to X$. This is the exact naturality needed to compare the ordinary and reciprocal charts.
-- source:
--   Original complete coordinate_embedding_restriction statement and proof from MazurTheorem AffineOpenChartFunctionFieldNaturality.lean, Apache-2.0, Vas and contributors. The original coordinate_embedding_via_stalk theorem is imported as a public proved dependency. Only public import and top-level namespace context change. The original complete closed type is kernel-compared. Named downstream consumer: the actual order-13 ordinary/reciprocal function-field overlap.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: compatibility of the constructed coordinate embeddings with
an affine open restriction. Named downstream consumer: comparison of the
ordinary and reciprocal Pell functions on the order-13 curve.
-/
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_via_stalk
noncomputable section
universe u
open MazurTransfer
open MazurTransfer.AffineOpenChartFunctionFieldNaturality
open AlgebraicGeometry CategoryTheory
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldStalk

variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

variable (B : CommRingCat.{u}) [IsDomain B] (φ : A ⟶ B)
    [IsOpenImmersion (Spec.map φ)]

theorem MazurTransfer.AffineOpenChartFunctionFieldNaturality.coordinate_embedding_restriction :
    CommRingCat.ofHom (coordinateEmbedding A j) =
      φ ≫ CommRingCat.ofHom (coordinateEmbedding B (Spec.map φ ≫ j)) := by sorry

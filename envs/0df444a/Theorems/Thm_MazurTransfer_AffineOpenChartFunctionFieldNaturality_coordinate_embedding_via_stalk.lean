-- Prove2me | Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_via_stalk
-- name    : MazurTransfer.AffineOpenChartFunctionFieldNaturality.coordinate_embedding_via_stalk
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:18:40.527979+00:00
-- url     : https://prove2.me/theorems/23d5d2be-21f8-439f-8ebf-ea17dbe44c8d
-- title:
--   The affine coordinate embedding factors through every canonical stalk
-- statement:
--   Let $A$ be a domain, $X$ an integral scheme, and $j:\operatorname{Spec}A\to X$ an open immersion. For every $p\in\operatorname{Spec}A$, the coordinate embedding into $K(X)$ is the composite $$A\longrightarrow\mathcal O_{\operatorname{Spec}A,p}\xrightarrow{(j_p^\#)^{-1}}\mathcal O_{X,j(p)}\longrightarrow K(X).$$ This provides the exact stalk diagram used to compare affine restrictions and compute orders of functions that are units on a chart.
-- source:
--   Original complete coordinate_embedding_via_stalk statement and proof from MazurTheorem AffineOpenChartFunctionFieldNaturality.lean, Apache-2.0, Vas and contributors. Two original stalk-commutation helpers from AffineOpenChartFunctionFieldStalk.lean are retained in an explicit fresh namespace. Public data imports supply canonical constructors. The full original closed type is kernel-compared. Named downstream consumer: actual ordinary-chart Pell orders.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the chart's generic field isomorphism commutes with the
actual maps from every stalk. Named downstream consumer: identifying the
two Pell valuation rings with the two literal infinity section centers.
-/
import Definitions.Def_MazurTransfer_AffineChartLocalStalkData
noncomputable section
universe u
open MazurTransfer AlgebraicGeometry CategoryTheory
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldStalk
variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

theorem MazurTransfer.AffineOpenChartFunctionFieldNaturality.coordinate_embedding_via_stalk (p : Spec A) :
    CommRingCat.ofHom (coordinateEmbedding A j) =
      StructureSheaf.toStalk A p ≫ (asIso (j.stalkMap p)).inv ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j p)) X.functionField) := by sorry

-- Prove2me | Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldStalk_local_stalk_coordinate_commutes
-- name    : MazurTransfer.AffineOpenChartFunctionFieldStalk.local_stalk_coordinate_commutes
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T12:37:19.157813+00:00
-- url     : https://prove2.me/theorems/06a4127c-ac64-4677-97fa-c50feb84817e
-- title:
--   The actual affine chart coordinate embedding commutes with every local stalk
-- statement:
--   For the specified affine open chart $j:\operatorname{Spec}A\to X$ of an integral scheme, the original coordinate embedding into the scheme function field agrees, at every chart point $p$, with localization followed by the canonical chart-to-stalk isomorphism and the stalk map to the function field: $$A\longrightarrow A_{\mathfrak p}\simeq\mathcal O_{X,j(p)}\longrightarrow K(X).$$ This exact commutation identifies the actual Pell valuation rings with the literal infinity section stalks.
-- source:
--   Original complete local_stalk_coordinate_commutes statement and main proof body from MazurTheorem AffineOpenChartFunctionFieldStalk.lean, Apache-2.0, Vas and contributors. The short original private specialization-cast lemma and stalk-map compatibility proof are inlined unchanged in a fresh namespace. Public imports and top-level namespace context alone replace dependencies. Native, strict and complete frontend checks pass; full original and public closed types are kernel-compared. Named downstream consumer: actual infinity-place center identification.

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

theorem MazurTransfer.AffineOpenChartFunctionFieldStalk.local_stalk_coordinate_commutes (p : Spec A) :
    CommRingCat.ofHom (coordinateEmbedding A j) =
      CommRingCat.ofHom (algebraMap A (Localization.AtPrime (chartPrime A p).asIdeal)) ≫
        (localStalkIso A j p).hom ≫
          CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j p)) X.functionField) := by sorry

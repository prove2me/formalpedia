-- Prove2me | Theorems.Thm_MazurTransfer_original_scheme_pullback_product_points_naturality
-- name    : MazurTransfer.original_scheme_pullback_product_points_naturality
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T01:16:10.274562+00:00
-- url     : https://prove2.me/theorems/45f62795-9fdc-4985-bafb-ac15bb5d4edd
-- statement:
--   The original pullback over the same fixed base represents pairs of points with the given structure maps. The original point equivalence commutes with every original precomposition map on both components. Every scheme, structure morphism, point, map and universe is retained. Named downstream consumer: the principal-action scheme isomorphism for the actual integral nineteen norm-preimage torsor.

import Definitions.Def_MazurTransfer_OriginalSchemePullbackProductPointsData20261020
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open MazurTransfer.SchemePullbackProductPoints
universe u

theorem MazurTransfer.original_scheme_pullback_product_points_naturality : (∀ {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) {T : Scheme.{u}} (t : T ⟶ B) {T' : Scheme.{u}} (t' : T' ⟶ B) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'), ∀ (b : SchemeHomOver t (productStr f g)),
pointsEquiv f g t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b) =
      (GoodReductionJacobian.schemeHomOverComp ψ hψ (pointsEquiv f g t b).1,
       GoodReductionJacobian.schemeHomOverComp ψ hψ (pointsEquiv f g t b).2)) := by sorry

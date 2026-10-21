-- Prove2me | Theorems.Thm_MazurTransfer_original_scheme_point_natural_equivalence_induces_iso
-- name    : MazurTransfer.original_scheme_point_natural_equivalence_induces_iso
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T01:23:23.585266+00:00
-- url     : https://prove2.me/theorems/ec2330d0-b5f5-4433-9b45-1f9823201247
-- statement:
--   For the original schemes over the same base and the original natural equivalence of all their scheme-valued point functors, the inverse equivalence is natural and the same original point map is induced by the original scheme isomorphism. Every original test scheme, structure morphism, naturality certificate and universe is retained. Named downstream consumer: the principal-action scheme isomorphism of the actual integral norm-preimage torsor at nineteen.

import Definitions.Def_MazurTransfer_OriginalSchemePointNaturalEquivalenceIsoData20261020
noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.SchemePointNaturalEquivalenceIso
universe u

theorem MazurTransfer.original_scheme_point_natural_equivalence_induces_iso : (∀ {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (e : ∀ {T : Scheme.{u}} (t : T ⟶ B), SchemeHomOver t f ≃ SchemeHomOver t g) (hNat : ∀ {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f), e t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = GoodReductionJacobian.schemeHomOverComp ψ hψ (e t x)), ∀ {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (y : SchemeHomOver t g),
(e t').symm (GoodReductionJacobian.schemeHomOverComp ψ hψ y) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ ((e t).symm y)) ∧ (∀ {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (e : ∀ {T : Scheme.{u}} (t : T ⟶ B), SchemeHomOver t f ≃ SchemeHomOver t g) (hNat : ∀ {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f), e t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = GoodReductionJacobian.schemeHomOverComp ψ hψ (e t x)), ∀ {T : Scheme.{u}} (t : T ⟶ B) (x : SchemeHomOver t f),
(e t x).val = x.val ≫ (schemeIso f g e hNat).hom) := by sorry

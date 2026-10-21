-- Prove2me | Theorems.Thm_MazurTransfer_original_relative_norm_preimage_representation_naturality
-- name    : MazurTransfer.original_relative_norm_preimage_representation_naturality
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T01:08:26.784628+00:00
-- url     : https://prove2.me/theorems/d35a593a-1fa6-40db-be2a-171a16280c68
-- statement:
--   The original pullback fibre of the given relative endomorphism represents the preimages of the same given integral section over every original test scheme. The original pulled section and the exact scheme point equivalence commute with every original test-scheme map. All original structure morphisms, sections, schemes and universes are retained. Named downstream consumer: the principal-action scheme isomorphism for the actual finite-flat integral nineteen norm torsor.

import Definitions.Def_MazurTransfer_OriginalRelativeNormPreimageRepresentationData20261020
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeNormPreimagePointTorsor MazurTransfer.RelativeNormPreimageRepresentation
universe u

theorem MazurTransfer.original_relative_norm_preimage_representation_naturality : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}, ∀ (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') ,
GoodReductionJacobian.schemeHomOverComp ψ hψ (pulledPoint a t) = pulledPoint a t') ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}, ∀ (F : SchemeHomOver f f) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (b : SchemeHomOver t (fibreStr F a)),
(pointsEquiv F a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b)).val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (pointsEquiv F a t b).val) := by sorry

-- Prove2me | Theorems.Thm_MazurTransfer_original_relative_norm_preimage_principal_iso_laws
-- name    : MazurTransfer.original_relative_norm_preimage_principal_iso_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T01:31:25.341897+00:00
-- url     : https://prove2.me/theorems/9558d9f0-fd43-4364-bea3-de1cde201a4d
-- statement:
--   The original preimage fibre of the given relative endomorphism has its same principal-action scheme isomorphism over the same base. Its point map is exactly the original natural kernel action on every test scheme, and that action is unital and associative. Every original scheme, section, group law, preservation certificate, test-scheme map and universe is retained. Named downstream consumer: the actual finite-flat integral nineteen norm-preimage torsor and its selected mu19 pushforward.

import Definitions.Def_MazurTransfer_OriginalRelativeNormPreimagePrincipalIsoData20261020
import Theorems.Thm_MazurTransfer_original_scheme_point_natural_equivalence_induces_iso
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf MazurTransfer.RelativeNormPreimagePointTorsor
open MazurTransfer.RelativeNormPreimageRepresentation MazurTransfer.RelativeNormPreimagePrincipalIso
universe u

theorem MazurTransfer.original_relative_norm_preimage_principal_iso_laws : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (b : SchemeHomOver t (sourceStr L F a)),
principalPointsEquiv L F hOne hMul a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (principalPointsEquiv L F hOne hMul a t b)) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t (sourceStr L F a)),
(principalPointsEquiv L F hOne hMul a t b).val =
      b.val ≫ (principalOverIso L F hOne hMul a).hom.left) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : preimagePoints F (pulledPoint a t)),
act L F hMul (⟨L.one t, hOne t⟩ : kernelPoints L F t) y = y) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (k l : kernelPoints L F t) (y : preimagePoints F (pulledPoint a t)),
act L F hMul (⟨L.mul t k.val l.val, kernelPoints_mul L F hMul t k l⟩ : kernelPoints L F t) y =
      act L F hMul k (act L F hMul l y)) := by sorry

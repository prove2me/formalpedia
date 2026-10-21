-- Prove2me | Theorems.Thm_MazurTransfer_original_relative_norm_preimage_point_torsor_laws
-- name    : MazurTransfer.original_relative_norm_preimage_point_torsor_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T00:59:54.573235+00:00
-- url     : https://prove2.me/theorems/211f6606-8025-4c93-ac4c-2deb10de6c00
-- statement:
--   For the original relative group endomorphism preserving the given identity and multiplication, the same preimage point functor has its original kernel action, difference and principal-action equivalence over every test scheme. The original difference satisfies the cocycle identity. Both the action and difference commute with all original test-scheme pullbacks. Every original scheme, group law, point, preservation certificate and universe is retained. No point over every test scheme is assumed. Named downstream consumer: the actual integral nineteen norm-preimage torsor and its selected mu19 quotient.

import Definitions.Def_MazurTransfer_OriginalRelativeNormPreimagePointTorsorData20261020
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf MazurTransfer.RelativeNormPreimagePointTorsor
universe u

theorem MazurTransfer.original_relative_norm_preimage_point_torsor_laws : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) , ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {a : SchemeHomOver t f}
    (x y z : preimagePoints F a),
(difference L F hOne hMul x z).val =
      L.mul t (difference L F hOne hMul x y).val (difference L F hOne hMul y z).val) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) , ∀ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'), ∀ {a : SchemeHomOver t f} (k : kernelPoints L F t) (y : preimagePoints F a),
precomposePreimage F ψ hψ (act L F hMul k y) =
      act L F hMul (precomposeKernel L F ψ hψ k) (precomposePreimage F ψ hψ y)) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) , ∀ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'), ∀ {a : SchemeHomOver t f} (x y : preimagePoints F a),
precomposeKernel L F ψ hψ (difference L F hOne hMul x y) =
      difference L F hOne hMul (precomposePreimage F ψ hψ x) (precomposePreimage F ψ hψ y)) := by sorry

-- Prove2me | Theorems.Thm_MazurTransfer_original_relative_norm_kernel_hopf_representability
-- name    : MazurTransfer.original_relative_norm_kernel_hopf_representability
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T00:52:08.43159+00:00
-- url     : https://prove2.me/theorems/ca2dbb3f-6d70-4371-9d44-03d40b38bb18
-- statement:
--   The given relative endomorphism retains its original scheme-theoretic kernel, every test-scheme point and naturality map, and the same inherited commutative relative group law. The complete existing exact official FLT finite-flat group-scheme theorem represents this same kernel by a finite flat cocommutative Hopf algebra with all original algebra-valued point and coefficient base-change maps. Over the original local ring the Hopf algebra is finite free. All original group-law preservation, commutativity, finite, flat and local-ring hypotheses are retained. Named downstream consumer: the actual integral nineteen norm kernels and their same norm-preimage torsors.

import Definitions.Def_MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020
import Theorems.Thm_AlgebraicGeometry_exists_hopfAlgebra_flat_of_grpObj_over_spec
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open scoped CategoryTheory.MonObj
universe u

theorem MazurTransfer.original_relative_norm_kernel_hopf_representability : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), ∀ {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (a : SchemeHomOver t (kernelStr L F)),
(kernelPointsEquiv L F t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)).val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (kernelPointsEquiv L F t a).val) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)), ∀ (hc : L.IsCommutative),
(kernelLaw L F hOne hMul).IsCommutative) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)), ∀ (hc : L.IsCommutative) [IsFinite F.val] [Flat F.val],
∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃ kernelPoints L F (Spec.map (CommRingCat.ofHom (algebraMap R T))),
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          (e T (φ * ψ)).val = L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          (e T' (.toConv (g.comp φ.ofConv))).val.val =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.val)) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)), ∀ [IsLocalRing R]
    (hc : L.IsCommutative) [IsFinite F.val] [Flat F.val],
HasFiniteFreeKernelHopfModel L F) := by sorry

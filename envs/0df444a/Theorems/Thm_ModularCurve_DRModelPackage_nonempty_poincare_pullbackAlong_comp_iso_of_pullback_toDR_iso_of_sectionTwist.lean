-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_nonempty_poincare_pullbackAlong_comp_iso_of_pullback_toDR_iso_of_sectionTwist
-- name    : ModularCurve.DRModelPackage.nonempty_poincare_pullbackAlong_comp_iso_of_pullback_toDR_iso_of_sectionTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/ce920b50-cb14-50f2-9527-0428b00ee287
-- title:
--   Geometric-fibre transport of the Poincaré bundle with section twists
-- statement:
--   Fix a prime $p$ and a package $\mathfrak{X}$ of type `DRModelPackage p` for the two-chart integral model $\mathrm{DRModel}\,p$ of the modular function field, with structure morphism $\pi : \mathrm{DRModel}\,p \to \operatorname{Spec}\mathbb{Z}$ assumed proper; let $D$ be a relative $\mathrm{Pic}^0$ designation for $\pi$ (a scheme $D.P$ with a morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}\mathbb{Z}$ and a zero section), and let $hD$ witness that $D$ represents the subfunctor of line bundles on $\pi$ rigidified along $\mathfrak{X}.\varepsilon_{\mathrm{inf}}$ which are fibrewise algebraically equivalent to zero; $hD.\mathrm{poincare}$ is the corresponding rigidified bundle on $\mathrm{DRModel}\,p \times_{\operatorname{Spec}\mathbb{Z}} D.P$. Let $O$ be a domain, $z : \operatorname{Spec} O \to D.P$ a morphism over $\operatorname{Spec}\mathbb{Z}$, and $M$ a module sheaf on $\mathfrak{X}_O := \mathrm{DRModel}\,p \times_{\operatorname{Spec}\mathbb{Z}} \operatorname{Spec} O$ isomorphic to the pull-back of $hD.\mathrm{poincare}$ along $z$. Let $Y$ be a scheme, proper over $\operatorname{Spec} O$ via `toBase`, together with `toDR` $: Y \to \mathfrak{X}_O$ compatible with the two structure morphisms and restricting to an isomorphism over the basic open set $D(p) \subseteq \operatorname{Spec} O$, and let $L$ on $Y$ be isomorphic to the pull-back of $M$ along `toDR`. Let $m \in \mathbb{N}$, let $\sigma_0,\dots,\sigma_{m-1}$ be sections of `toBase`, and $\mathrm{pos},\mathrm{neg} : \mathrm{Fin}\,m \to \mathbb{N}$; assume that over the fraction field $F$ of $O$ the pull-back of $L$ to $Y \times_{\operatorname{Spec} O} \operatorname{Spec} F$ is isomorphic to $\bigotimes_j \bigl((\mathcal{I}_{\sigma_j}^{\mathrm{pos}_j})^{\vee} \otimes \mathcal{I}_{\sigma_j}^{\mathrm{neg}_j}\bigr)$, where $\mathcal{I}_{\sigma_j}$ is the ideal sheaf of the graph of $\sigma_j$ base-changed to $F$, the tensor product being taken as an iterated fold starting from the unit. Finally let $\tau : O \to \overline{\mathbb{Q}}$ and $\tau_F : F \to \overline{\mathbb{Q}}$ be ring homomorphisms with $\tau_F \circ (O \to F) = \tau$, and let $q_0,\dots,q_{m-1}$ be $\overline{\mathbb{Q}}$-points of the curve model $\mathfrak{X}.M_\eta$ such that, for each $j$, the image of $q_j$ in $\mathfrak{X}_O$ under $\mathfrak{X}.e_\eta$ followed by the base-change map induced by $\operatorname{Spec}\tau$ coincides with $\operatorname{Spec}\tau$ followed by $\sigma_j$ followed by `toDR`. The conclusion is that the pull-back of $hD.\mathrm{poincare}$ along the $\overline{\mathbb{Q}}$-point $\operatorname{Spec}\tau$ followed by $z$ of $D.P$ is isomorphic to $\bigotimes_j \bigl((\mathcal{I}_{q_j}^{\mathrm{pos}_j})^{\vee} \otimes \mathcal{I}_{q_j}^{\mathrm{neg}_j}\bigr)$ on $\mathrm{DRModel}\,p \times_{\operatorname{Spec}\mathbb{Z}} \operatorname{Spec}\overline{\mathbb{Q}}$, where $\mathcal{I}_{q_j}$ is the ideal sheaf of the relative effective Cartier divisor of degree one cut out by the point $q_j$, again folded from the unit.
--
--   This is the transport step that moves a line-bundle identity, available after pulling back to a proper model $Y$ over $\operatorname{Spec} O$ which is an isomorphism away from $p$ and after correcting by twists along sections, to the geometric fibre over $\overline{\mathbb{Q}}$, where the section twists become the point bundles of the specialised points $q_j$ on the curve model $\mathfrak{X}.M_\eta$. It is used in the proof of [`ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective`](thm.html#ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective), which produces $O$-points of the representing object $D.P$ from divisor classes of degree zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_nonempty_poincare_pullbackAlong_comp_iso_of_pullback_toDR_iso_of_sectionTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization

theorem ModularCurve.DRModelPackage.nonempty_poincare_pullbackAlong_comp_iso_of_pullback_toDR_iso_of_sectionTwist
    (p : ℕ) [Fact p.Prime]
    (𝔛 : DRModelPackage p)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    [IsProper (DRModel.toBase p)]
    (O : Type) [CommRing O] [IsDomain O]
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) D.toBase)
    (M : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Modules)
    (eMz : Nonempty ((hD.poincare.pullbackAlong z).L ≅ M))
    (Y : Scheme.{0}) (toBase : Y ⟶ Spec (CommRingCat.of O))
    (toDR : Y ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
    (toDR_over : toDR ≫ pullback.snd _ _ = toBase) [IsProper toBase]
    (toDR_iso_generic : IsIso (toDR ∣_ (pullback.snd (DRModel.toBase p) _ ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))))
    (L : Y.Modules) (eM : Nonempty ((Scheme.Modules.pullback toDR).obj M ≅ L))
    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) toBase) (pos neg : Fin m → ℕ)
    (hLgen : Nonempty ((Scheme.Modules.pullback (pullback.fst toBase
          (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))).obj L ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))) (pos j) ⊗
              ((sectionIdeal toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback toBase (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))).Modules)))
    (τ : O →+* AlgebraicClosure ℚ) (τF : FractionRing O →+* AlgebraicClosure ℚ)
    (hτ : τF.comp (algebraMap O (FractionRing O)) = τ)
    (q : Fin m → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (hqσ : ∀ j, (q j).1 ≫ 𝔛.eη ≫
        pullback.map (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
          (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) (𝟙 _) (Spec.map (CommRingCat.ofHom τ)) (𝟙 _)
          (by simp)
          (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext_int _ _) =
      Spec.map (CommRingCat.ofHom τ) ≫ (σ j).1 ≫ toDR) :
    Nonempty ((hD.poincare.pullbackAlong ⟨Spec.map (CommRingCat.ofHom τ) ≫ z.1, by
        rw [Category.assoc, z.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext_int _ _⟩).L ≅
      (List.finRange m).foldr (fun j M =>
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
              (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2])).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
              (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2])).I ^ (neg j)).module ⊗ M)
        (𝟙_ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).Modules)) := by sorry

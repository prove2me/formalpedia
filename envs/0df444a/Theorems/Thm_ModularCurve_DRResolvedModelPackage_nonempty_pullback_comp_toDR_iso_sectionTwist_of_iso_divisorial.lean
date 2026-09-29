-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackage_nonempty_pullback_comp_toDR_iso_sectionTwist_of_iso_divisorial
-- name    : ModularCurve.DRResolvedModelPackage.nonempty_pullback_comp_toDR_iso_sectionTwist_of_iso_divisorial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/6cda05ac-8de3-5c24-b529-ae7a287d2776
-- title:
--   Generic fibre of a bundle descended through the resolution
-- statement:
--   Fix a prime $p$, a package $\mathfrak{X}$ of Deligne–Rapoport model data over $\mathbb{Z}$ for level $p$, a domain $O$, an algebraically closed field $\kappa$ of characteristic $p$, a ring homomorphism $O \to \kappa$, and a resolved model package $\mathfrak{X}_{\mathrm{reg}}$ for these data, with structure morphisms $\mathfrak{X}_{\mathrm{reg}}.\mathrm{toBase} : Y \to \operatorname{Spec} O$ and $\mathfrak{X}_{\mathrm{reg}}.\mathrm{toDR} : Y \to \mathfrak{X}_O$, where $\mathfrak{X}_O$ denotes the base change of `DRModel.toBase p` along $\operatorname{Spec} O \to \operatorname{Spec}\mathbb{Z}$. Let $m \in \mathbb{N}$ and let $\sigma_0,\dots,\sigma_{m-1}$ be sections of $\mathfrak{X}_{\mathrm{reg}}.\mathrm{toBase}$, i.e. morphisms $\operatorname{Spec} O \to Y$ composing with $\mathrm{toBase}$ to the identity; let $\mathrm{pos}, \mathrm{neg} : \mathrm{Fin}\,m \to \mathbb{N}$ and let $a^{+}, a^{-}$ assign natural numbers to the index set `X0MqComponents 𝔛reg.width` of vertical components of $\mathfrak{X}_{\mathrm{reg}}$. Let $M$ be a sheaf of modules on $\mathfrak{X}_O$. Write $L$ for the module on $Y$ obtained by folding, over $j = 0,\dots,m-1$, the operation $N \mapsto (\ker\sigma_j)^{\mathrm{pos}\,j\,\vee} \otimes (\ker\sigma_j)^{\mathrm{neg}\,j} \otimes N$ (for an ideal sheaf $I$, $I$ is taken as a module via `module` and its dual via `invModule`) starting from $(\prod_F \mathfrak{X}_{\mathrm{reg}}.\mathrm{comp}\,F^{a^{+}F})^{\vee} \otimes \prod_F \mathfrak{X}_{\mathrm{reg}}.\mathrm{comp}\,F^{a^{-}F}$. Assume, first, that the pullback of $M$ along $\mathrm{toDR}$ is isomorphic to $L$, and second, that the pullback of $L$ along the first projection $Y_{\mathrm{Frac}\,O} \to Y$ is isomorphic to the corresponding fold with each factor replaced by $\mathrm{sectionTwist}(\sigma_j,\mathrm{pos}\,j) \otimes (\mathrm{sectionIdeal}(\sigma_j))^{\mathrm{neg}\,j}$, starting from the unit object; here $\mathrm{sectionIdeal}$ is the kernel ideal sheaf of the rigidified section on $Y_{\mathrm{Frac}\,O}$ and $\mathrm{sectionTwist}(\sigma_j,r)$ is the dual of its $r$-th power. The conclusion is that the pullback of $M$ along the composite of $Y_{\mathrm{Frac}\,O} \to Y$ with $\mathrm{toDR}$ is isomorphic to that same generic-fibre fold. All three isomorphism assertions are stated as nonemptiness of the respective types of isomorphisms.
--
--   This is the transitivity step that converts a divisorial identification of a line bundle on the resolved model into the corresponding identification on the generic fibre, where the vertical components of the special fibre no longer contribute and the section ideals appear as section twists. It supplies the generic-fibre hypothesis used by [`ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective`](thm.html#ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackage_nonempty_pullback_comp_toDR_iso_sectionTwist_of_iso_divisorial.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
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
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization

set_option maxHeartbeats 800000 in

theorem ModularCurve.DRResolvedModelPackage.nonempty_pullback_comp_toDR_iso_sectionTwist_of_iso_divisorial
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (aplus aminus : X0MqComponents 𝔛reg.width → ℕ)
    (M : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Modules)
    (eM : Nonempty ((Scheme.Modules.pullback 𝔛reg.toDR).obj M ≅
        ((List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
          ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module))))
    (hLgen : Nonempty ((Scheme.Modules.pullback (pullback.fst 𝔛reg.toBase
          (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))).obj
            ((List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
          ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module)) ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))) (pos j) ⊗
              ((sectionIdeal 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))).Modules))) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst 𝔛reg.toBase
          (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))) ≫ 𝔛reg.toDR)).obj M ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))) (pos j) ⊗
              ((sectionIdeal 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))).Modules)) := by sorry

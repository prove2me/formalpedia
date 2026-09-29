-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_atkinLehnerHom_classifies_pullback
-- name    : ModularCurve.DRModelPackageLevel.exists_atkinLehnerHom_classifies_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/721969b9-00b7-5bd8-ac81-fb3d20f18a97
-- title:
--   Atkin–Lehner endomorphism of the relative Pic⁰ representing scheme
-- statement:
--   Fix a nonzero natural number $N_0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀` for the level-$N_0p$ model `X N₀ p` with structure morphism `toBase N₀ p` to $\mathrm{Spec}$ of the base ring `R p`; among its data are the section `𝔓.εinf` of `toBase N₀ p`, and the endomorphism `𝔓.w.hom` of `X N₀ p` together with `𝔓.w_over`, which says that `𝔓.w.hom` followed by `toBase N₀ p` is again `toBase N₀ p`. Let `D` be a designation, i.e. a scheme with a morphism `D.toBase` to $\mathrm{Spec}$ of `R p` and a section `D.zeroSection` of it, and let `hD` assert that `D` represents the subfunctor of `𝔓.εinf`-rigidified line bundles on `X N₀ p` cut out by the condition `FibrewiseAlgEquivZero`: `hD` provides a Poincaré bundle `hD.poincare` over `D.toBase` satisfying that condition, the property that every rigidified bundle satisfying it over a base `t : T ⟶ Spec (R p)` is the pullback of `hD.poincare` along a unique $T$-point of `D` over the base, and that the pullback along `D.zeroSection` is the unit bundle. Then there exists a morphism `wstar` from `D` to itself over $\mathrm{Spec}$ of `R p` with three properties. First, for every scheme $T$, every `t : T ⟶ Spec (R p)` and every $T$-point `a` of `D` over the base, the pullback of `hD.poincare` along `a` followed by `wstar` is isomorphic to the rigidification along `rigSection (toBase N₀ p) t 𝔓.εinf` — that is, the tensor product with the pullback along `pullback.snd (toBase N₀ p) t` of the dual of the restriction along that section — of the pullback of $a^{*}$`hD.poincare` along the base-changed morphism `curveChange 𝔓.w.hom 𝔓.w_over t`. Secondly, `wstar` is a homomorphism for the relative group law on `D` furnished by `hD` through `algEquivZeroGroupCut`: for all `t` and all $T$-points `x`, `y`, the product of `x` and `y` followed by `wstar` equals the product of `x` followed by `wstar` and `y` followed by `wstar`. Thirdly, `D.zeroSection` followed by `wstar` equals `D.zeroSection`.
--
--   This is the Atkin–Lehner involution $w_*$ acting on the scheme representing the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model at level $N_0p$ over the base ring, characterised by the transform it induces on rigidified line bundles: pullback along $w$ followed by re-rigidification along the section `𝔓.εinf`. It is used in the construction of the Hecke action on this representing scheme, via [`ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp`](thm.html#ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_atkinLehnerHom_classifies_pullback.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.exists_atkinLehnerHom_classifies_pullback
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D) :
    ∃ wstar : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a wstar)).L ≅
          Scheme.Modules.rigidify (rigSection (toBase N₀ p) t 𝔓.εinf) (pullback.snd (toBase N₀ p) t)
            ((Scheme.Modules.pullback (curveChange 𝔓.w.hom 𝔓.w_over t)).obj (hD.poincare.pullbackAlong a).L))) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) wstar =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t
            (NeronModelInfra.schemeHomOverComp x wstar) (NeronModelInfra.schemeHomOverComp y wstar)) ∧
      D.zeroSection ≫ wstar.1 = D.zeroSection := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_degeneracyPullbackHom_classifies_pullback
-- name    : ModularCurve.DRModelPackageLevel.exists_degeneracyPullbackHom_classifies_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/ac687186-98a3-5691-8296-cd714bd1e342
-- title:
--   Existence of the degeneracy pullback homomorphism β^*
-- statement:
--   Fix a positive integer $N_0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a `DRModelPackageLevel` for these data, so that in particular it supplies a section `𝔓.εinf` of the structure map `toBase N₀ p` of the level-$N_0p$ Igusa scheme over $\operatorname{Spec} R_p$ and a morphism `𝔓.πw` from that scheme to the level-$N_0$ scheme `X0 N₀ p` compatible with the two structure maps `toBase N₀ p` and `toBase0 N₀ p`. Let $D$ be a pointed $R_p$-scheme designation (a scheme with a structure map to $\operatorname{Spec} R_p$ and a zero section splitting it) for `toBase N₀ p`, and let `hD` witness that $D$ represents, with Poincaré bundle `hD.poincare`, the functor of line bundles on `pullback (toBase N₀ p) t` rigidified along `𝔓.εinf` that are fibrewise algebraically equivalent to zero; let $\varepsilon_0$ be a section of `toBase0 N₀ p`, and let $D_0$, `hD₀` be the corresponding data for `toBase0 N₀ p` and $\varepsilon_0$. Then there exists a morphism $\beta^* \colon D_0 \to D$ over $\operatorname{Spec} R_p$ such that: for every scheme $T$ with a map $t$ to $\operatorname{Spec} R_p$ and every $T$-point $b$ of $D_0$ over $t$, the pullback of `hD.poincare` along $b$ followed by $\beta^*$ has underlying module isomorphic to the rigidification along `rigSection (toBase N₀ p) t 𝔓.εinf` (that is, tensored with the pullback along `pullback.snd (toBase N₀ p) t` of the dual of the restriction along that section) of the pullback along `curveChange 𝔓.πw.1 𝔓.πw.2 t` of $b^*$`hD₀.poincare`; $\beta^*$ is a homomorphism for the relative group laws obtained from the two representability witnesses for the fibrewise-algebraically-trivial group cut, i.e. $(xy)\beta^* = (x\beta^*)(y\beta^*)$ for all $T$-points $x,y$ of $D_0$; and $\beta^*$ carries the zero section of $D_0$ to that of $D$.
--
--   This is the degeneracy pullback map on representing schemes of the relative $\mathrm{Pic}^0$ functors: pulling back line bundles along the degeneracy morphism $X(N_0p) \to X_0(N_0)$ over $\mathbf{Z}_{(p)}$ and re-rigidifying along the section at infinity is classified by a morphism of the representing pointed schemes, compatible with the group laws and the zero sections. It is used in the construction of Hecke-type correspondences on the relative Jacobian, being cited by [`ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp`](thm.html#ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_degeneracyPullbackHom_classifies_pullback.lean

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

theorem ModularCurve.DRModelPackageLevel.exists_degeneracyPullbackHom_classifies_pullback
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
    (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀) :
    ∃ βstar : SchemeHomOver D₀.toBase D.toBase,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b βstar)).L ≅
          Scheme.Modules.rigidify (rigSection (toBase N₀ p) t 𝔓.εinf) (pullback.snd (toBase N₀ p) t)
            ((Scheme.Modules.pullback (curveChange 𝔓.πw.1 𝔓.πw.2 t)).obj (hD₀.poincare.pullbackAlong b).L))) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D₀.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul t x y) βstar =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t
            (NeronModelInfra.schemeHomOverComp x βstar) (NeronModelInfra.schemeHomOverComp y βstar)) ∧
      D₀.zeroSection ≫ βstar.1 = D.zeroSection := by sorry

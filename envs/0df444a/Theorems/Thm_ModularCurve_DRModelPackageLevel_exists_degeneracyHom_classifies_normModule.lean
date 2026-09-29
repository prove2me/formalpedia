-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_degeneracyHom_classifies_normModule
-- name    : ModularCurve.DRModelPackageLevel.exists_degeneracyHom_classifies_normModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/9822d84a-4cd2-5af4-bf93-d04dc864bf40
-- title:
--   Degeneracy morphisms on Pic⁰ representing schemes as norm maps
-- statement:
--   Let $N_0$ be a nonzero natural number and $p$ a prime with $p \nmid N_0$, and let $\mathfrak P$ be a level-$N_0p$ Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀`, whose data include the Igusa scheme $X(N_0,p)$ with structure morphism `toBase N₀ p` to $\operatorname{Spec} R(p)$, a section `𝔓.εinf` of it, and two morphisms `𝔓.π` and `𝔓.πw` from $X(N_0,p)$ to $X_0(N_0,p)$ over $\operatorname{Spec} R(p)$. Let $D$ be a relative $\mathrm{Pic}^0$ designation for `toBase N₀ p`, i.e. a scheme with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} R(p)$ and a section `D.zeroSection` of it, and let $h_D$ exhibit $D$ as representing the cut `algEquivZeroCut`: a rigidified line bundle (the Poincaré bundle) on the fibre product of $X(N_0,p)$ with $D$, fibrewise algebraically equivalent to zero, such that every rigidified line bundle with that property on the pullback along any $t : T \to \operatorname{Spec} R(p)$ is the pullback of the Poincaré bundle along a unique $T$-point of $D$ over $t$, the zero section giving the unit. Let $\varepsilon_0$ be a section of `toBase0 N₀ p`, and let $D_0$, $h_{D_0}$ be the corresponding data for $(X_0(N_0,p),\varepsilon_0)$. Assume `𝔓.π.1` is finite, flat and locally of finite presentation, with $\operatorname{finrank} = p+1$ at every point of $X_0(N_0,p)$; these last four hypotheses are imposed on `𝔓.π.1` only. Then there exist two morphisms $\delta_0,\delta_1$ from $D$ to $D_0$ over $\operatorname{Spec} R(p)$ such that: for every scheme $T$, every $t : T \to \operatorname{Spec} R(p)$ and every $T$-point $a$ of $D$ over $t$, the pullback of the Poincaré bundle of $D_0$ along $a$ followed by $\delta_0$ (respectively $\delta_1$) is isomorphic to the `rigidify` along `rigSection (toBase0 N₀ p) t ε₀` and `pullback.snd` of the `normModule` in degree $p+1$, namely $\det_{p+1}(\pi_*L) \otimes \det_{p+1}(\pi_*\mathcal O)^{\vee}$, of the pullback $L$ of the Poincaré bundle of $D$ along $a$, taken along the base change of `𝔓.π.1` (respectively `𝔓.πw.1`) to $T$; each $\delta_i$ is a homomorphism for the relative group laws on $T$-points induced by $h_D$ and $h_{D_0}$ for the cut `algEquivZeroGroupCut`; and each $\delta_i$ carries `D.zeroSection` to `D₀.zeroSection`.
--
--   This is the construction of the two degeneracy morphisms $\alpha_*,\beta_*$ from the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model at level $N_0p$ to that at level $N_0$, realised through the norm of invertible sheaves along the finite locally free degeneracy maps $\pi$ and $w\pi$ of degree $p+1$, and pinned down by the representability of the two relative $\mathrm{Pic}^0$ functors. It is used by [`ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp`](thm.html#ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp) and by [`ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_degeneracyHom_classifies_normModule.lean

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

theorem ModularCurve.DRModelPackageLevel.exists_degeneracyHom_classifies_normModule
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
    (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)

    [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1] (hrk : ∀ x, 𝔓.π.1.finrank x = p + 1) :
    ∃ δ : Fin 2 → SchemeHomOver D.toBase D₀.toBase,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.π.1 𝔓.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L))) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.πw.1 𝔓.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L))) ∧
      (∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) (δ i) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul t
            (NeronModelInfra.schemeHomOverComp x (δ i)) (NeronModelInfra.schemeHomOverComp y (δ i))) ∧
      (∀ i : Fin 2, D.zeroSection ≫ (δ i).1 = D₀.zeroSection) := by sorry

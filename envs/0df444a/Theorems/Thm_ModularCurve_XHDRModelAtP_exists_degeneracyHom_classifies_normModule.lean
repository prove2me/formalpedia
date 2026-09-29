-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_degeneracyHom_classifies_normModule
-- name    : ModularCurve.XHDRModelAtP.exists_degeneracyHom_classifies_normModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/94002929-7e47-599f-8af3-759b038b3ff6
-- title:
--   Degeneracy morphisms of relative Pic⁰ as norm maps
-- statement:
--   Fix a prime $p$, a nonzero natural number $M$ with $p \mid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$; assume the Laurent series $j$, `jqModC ℚ`, lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be a datum of type `XHDRModelAtP p M H hpM hj`, which bundles the two-chart integral models over $R_p$ of the curves at levels `ΓM M H` and `ΓN p M H hpM` together with the morphisms $\mathfrak{X}.\pi$ and $\mathfrak{X}.\pi_w$ over $\operatorname{Spec} R_p$ and the section $\mathfrak{X}.\varepsilon_{\inf}$. Let $D$ be a designation (a scheme over $\operatorname{Spec} R_p$ with a section of its structure morphism) for the upper-level curve `toBase p (ΓM M H) hj`, and let $hD$ exhibit $D$, with its Poincaré rigidified line bundle, as representing the functor of rigidified line bundles on the base changes of that curve whose fibres over algebraically closed points are algebraically equivalent to zero; let $\varepsilon_0$ be a section of the lower-level curve `toBase p (ΓN p M H hpM) hj` over $\operatorname{Spec} R_p$ and let $D_0$, $hD_0$ be a corresponding designation and representability datum for that curve with rigidification $\varepsilon_0$. Assume $\mathfrak{X}.\pi$ is finite, flat and locally of finite presentation, of constant rank $p+1$ at every point. Then there exist two morphisms $\delta_0,\delta_1 : D.P \to D_0.P$ over $\operatorname{Spec} R_p$ such that: for every scheme $T$, every $t : T \to \operatorname{Spec} R_p$ and every $T$-point $a$ of $D$ over $t$, the pullback along $a$ followed by $\delta_0$ of the Poincaré bundle of $D_0$ is isomorphic to the rigidification, along the section `rigSection` of $\varepsilon_0$ and the projection `pullback.snd`, of the norm module $\det_{p+1}(\pi_{T*}\mathcal{L}) \otimes \det_{p+1}(\pi_{T*}\mathcal{O})^\vee$ of the pullback $\mathcal{L}$ of the Poincaré bundle of $D$ along $a$, where $\pi_T$ is the base change `curveChange` of $\mathfrak{X}.\pi$ to $T$; the same holds for $\delta_1$ with $\mathfrak{X}.\pi_w$ in place of $\mathfrak{X}.\pi$; each $\delta_i$ is compatible with the relative group laws on $T$-points induced by $hD$ and $hD_0$ for the algebraically-equivalent-to-zero cut, i.e. composing a product with $\delta_i$ gives the product of the composites; and $D.\mathrm{zeroSection}$ followed by $\delta_i$ equals $D_0.\mathrm{zeroSection}$.
--
--   This constructs, at the level of the schemes representing the algebraically trivial part of the relative Picard functor, the two degeneracy homomorphisms between the Jacobians of the modular curves of level $\Gamma_H(M)$ and of the lower level, obtained as norms of line bundles along the finite locally free forgetful morphism and along its composite with the Atkin–Lehner involution. It is used in the level-lowering input at $p$, and is cited by [`ModularCurve.XHDRModelAtP.exists_degeneracyHom_mul_pts_special`](thm.html#ModularCurve.XHDRModelAtP.exists_degeneracyHom_mul_pts_special).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_degeneracyHom_classifies_normModule.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
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
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_degeneracyHom_classifies_normModule
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)

    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓN p M H hpM) hj))
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) ε₀ (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) ε₀) D₀)

    [IsFinite 𝔛.π.1] [Flat 𝔛.π.1] [LocallyOfFinitePresentation 𝔛.π.1] (hrk : ∀ x, 𝔛.π.1.finrank x = p + 1) :
    ∃ δ : Fin 2 → SchemeHomOver D.toBase D₀.toBase,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase p (ΓN p M H hpM) hj) t ε₀) (pullback.snd (toBase p (ΓN p M H hpM) hj) t)
          (Scheme.Modules.normModule (curveChange 𝔛.π.1 𝔛.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L))) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase p (ΓN p M H hpM) hj) t ε₀) (pullback.snd (toBase p (ΓN p M H hpM) hj) t)
          (Scheme.Modules.normModule (curveChange 𝔛.πw.1 𝔛.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L))) ∧
      (∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) (δ i) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul t
            (NeronModelInfra.schemeHomOverComp x (δ i)) (NeronModelInfra.schemeHomOverComp y (δ i))) ∧
      (∀ i : Fin 2, D.zeroSection ≫ (δ i).1 = D₀.zeroSection) := by sorry

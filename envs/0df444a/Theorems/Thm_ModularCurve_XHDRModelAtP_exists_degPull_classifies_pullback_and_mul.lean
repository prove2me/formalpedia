-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_degPull_classifies_pullback_and_mul
-- name    : ModularCurve.XHDRModelAtP.exists_degPull_classifies_pullback_and_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/95070e51-8922-5cb8-981a-e750b33b604a
-- title:
--   Degeneracy pull-backs between relative Pic⁰ representing objects
-- statement:
--   Fix a prime $p$, a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a witness `hj` that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field of the full modular group. Let $\mathfrak{X}$ be a model-at-$p$ package `XHDRModelAtP p M H hpM hj`, which supplies in particular a section $\varepsilon_\infty$ of the two-chart integral model $c_M =$ `toBase p (ΓM M H) hj` over `Spec (R p)` and two morphisms $\pi, \pi_w$ from the $\Gamma_M$-model to the $\Gamma_N$-model $c_N =$ `toBase p (ΓN p M H hpM) hj` over `Spec (R p)`. Let $D$ be a relative $\mathrm{Pic}^0$ designation for $c_N$ — a scheme with a structure map to `Spec (R p)` and a zero section — together with `hD`, asserting that $D$ represents the functor of rigidified line bundles on base changes of $c_M$ along $\varepsilon_\infty$ which are fibrewise algebraically equivalent to zero; let $D_0$, `hD₀` be the corresponding data for $c_N$ with the section $\varepsilon_\infty$ followed by $\pi$. Then there is a family $\mathrm{degPull} : \mathrm{Fin}\,2 \to$ morphisms $D_0 \to D$ over `Spec (R p)` such that for each $i$ (with $\pi$ for $i=0$ and $\pi_w$ otherwise): (i) for every $T$ with $t : T \to$ `Spec (R p)` and every $T$-point $b$ of $D_0$ over $t$, the Poincaré bundle of `hD` pulled back along $b$ followed by $\mathrm{degPull}_i$ is isomorphic to the rigidification (tensoring with the pull-back along `pullback.snd` of the dual of the restriction to `rigSection`) of the pull-back, along the curve-change map induced by $\pi$ resp. $\pi_w$ over $t$, of the Poincaré bundle of `hD₀` pulled back along $b$; (ii) composition with $\mathrm{degPull}_i$ is a homomorphism for the relative group laws on $D_0$ and $D$ coming from `hD₀` and `hD` via the cut `algEquivZeroGroupCut`; (iii) the zero section of $D_0$ followed by $\mathrm{degPull}_i$ is the zero section of $D$.
--
--   This is the integral form, over the base `R p`, of the statement that the two degeneracy maps between the modular curves of level $\Gamma_H(M)$ and the lower level $\Gamma_N$ induce by pull-back of divisor classes homomorphisms of the relative $\mathrm{Pic}^0$ schemes, compatible with the group laws and the zero sections. It feeds the comparison of the Jacobians at level $M$ and the lower level used in the Néron-model dictionary, being cited by [`ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords`](thm.html#ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords) and by [`ModularCurve.XHDRModelAtP.degPull_mul_and_zeroSection_comp_of_classifies_pullback`](thm.html#ModularCurve.XHDRModelAtP.degPull_mul_and_zeroSection_comp_of_classifies_pullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_degPull_classifies_pullback_and_mul.lean

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
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_degPull_classifies_pullback_and_mul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀) :
    ∃ degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase,

      (∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L))) ∧

      (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver s D₀.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul s x y) (degPull i) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
            (NeronModelInfra.schemeHomOverComp x (degPull i)) (NeronModelInfra.schemeHomOverComp y (degPull i))) ∧

      (∀ i : Fin 2, D₀.zeroSection ≫ (degPull i).1 = D.zeroSection) := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_degPull_mul_and_zeroSection_comp_of_classifies_pullback
-- name    : ModularCurve.XHDRModelAtP.degPull_mul_and_zeroSection_comp_of_classifies_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/07fb0a29-b9d9-5ec4-b025-af348b5aec80
-- title:
--   Classifying morphisms D₀ → D respect group law and zero
-- statement:
--   Fix a prime $p$, a positive integer $M$ divisible by $p$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field of the full modular group; let $\mathfrak{X}$ be a Deligne–Rapoport-type model datum `XHDRModelAtP p M H hpM hj`, whose data include the section $\varepsilon_\infty$ of the curve `toBase p (ΓM M H) hj` over $\operatorname{Spec}(R\,p)$ and the degeneracy morphisms $\pi$ and $\pi_w$ from the $\Gamma_N$-level curve to the $\Gamma_M$-level curve. Let $D$ be a relative $\mathrm{Pic}^0$ designation for the $\Gamma_M$-level curve, represented, in the sense of `RepresentsRelSubPic`, for the sub-Picard condition `algEquivZeroCut` (fibrewise algebraic equivalence to zero of rigidified line bundles) with $\varepsilon_\infty$ as rigidifying section, with Poincaré bundle `hD.poincare`; let $D_0$ be a designation for the $\Gamma_N$-level curve, similarly represented with rigidifying section $\varepsilon_\infty$ composed with $\pi$, with Poincaré bundle `hD₀.poincare`. Let $\mathrm{degPull}_i$, $i \in \{0,1\}$, be morphisms $D_0 \to D$ over $\operatorname{Spec}(R\,p)$, and assume each classifies the expected bundle: for every scheme $T$ over $\operatorname{Spec}(R\,p)$ via $t$ and every $T$-point $b$ of $D_0$ over $t$, the line bundle underlying the pullback of `hD.poincare` along $b$ followed by $\mathrm{degPull}_i$ is isomorphic to the re-rigidification, in the sense of `Scheme.Modules.rigidify` along the section `rigSection` attached to $\varepsilon_\infty$ and the second projection, of the pullback along `curveChange` of ($\pi$ for $i=0$, $\pi_w$ for $i=1$) of the bundle underlying `hD₀.poincare.pullbackAlong b`. The conclusion is twofold: first, each $\mathrm{degPull}_i$ is multiplicative for the relative group laws supplied by the two representability data for `algEquivZeroGroupCut`, that is, for every base morphism $s$ and all $T$-points $x, y$ of $D_0$ the product $x \cdot y$ followed by $\mathrm{degPull}_i$ equals the product of $x$ followed by $\mathrm{degPull}_i$ and $y$ followed by $\mathrm{degPull}_i$; second, `D₀.zeroSection` followed by $\mathrm{degPull}_i$ equals `D.zeroSection`.
--
--   This says that the two degeneracy maps on relative Jacobians, characterised by the bundle they classify, are homomorphisms of the relative group schemes and send zero to zero; it upgrades the classifying property alone into the group-theoretic statement, so that a morphism given only by its classifying property may be used as a homomorphism. It is used in identifying the maps induced on $\mathrm{Pic}^0$ by $\pi$ and $\pi \circ w$ on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_degPull_mul_and_zeroSection_comp_of_classifies_pullback.lean

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
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.degPull_mul_and_zeroSection_comp_of_classifies_pullback
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)
    (degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase)
    (hdegPull : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L))) :

    (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver s D₀.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul s x y) (degPull i) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
          (NeronModelInfra.schemeHomOverComp x (degPull i)) (NeronModelInfra.schemeHomOverComp y (degPull i))) ∧

    (∀ i : Fin 2, D₀.zeroSection ≫ (degPull i).1 = D.zeroSection) := by sorry

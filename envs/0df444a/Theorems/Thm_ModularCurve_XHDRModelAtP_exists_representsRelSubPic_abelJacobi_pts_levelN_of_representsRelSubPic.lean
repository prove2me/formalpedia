-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic
-- name    : ModularCurve.XHDRModelAtP.exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/2cfd72a5-e9b6-55d7-8cbc-b504cc1d97dd
-- title:
--   Generic fibre and points dictionary for the level-M/p Pic⁰ object
-- statement:
--   Fix a prime $p$, a nonzero modulus $M$ with $p \mid M$ and $M/p$ nonzero, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis $hj$ that the $q$-expansion of $j$ lies in the function field of the full modular group; let $\mathfrak{X}$ be an `XHDRModelAtP` bundle for these data, and assume that the level-$\Gamma_N(p,M,H)$ integral model $c =$ `toBase p (ΓN p M H hpM) hj` over $R_p$ is proper and that its base change to $\mathbb{Q}$ is smooth of relative dimension $1$ and geometrically integral. Further data: a curve model $\mathrm{Meta}_0$ over $\overline{\mathbb{Q}}$ of the field $\overline{\mathbb{Q}}\cdot F(\Gamma_{H'}(M/p))$, where $H'$ is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$; an isomorphism $e_0$ from $\mathrm{Meta}_0.C$ to the fibre product of $c$ with $\operatorname{Spec}\overline{\mathbb{Q}}$, compatible with the structure morphisms; a $\mathrm{Pic}^0$ designation $D_0$ over $R_p$ for $c$ (a scheme $D_0.P$ with a morphism $D_0.\mathrm{toBase}$ to $\operatorname{Spec} R_p$ and a zero section), together with a witness $h_{D_0}$ that $D_0$ represents the rigidified line bundles on $c$, rigidified along the section $\varepsilon_\infty$ followed by $\pi$, that are fibrewise algebraically equivalent to zero; and the assumptions that $D_0.\mathrm{toBase}$ is smooth and that its base change to $\mathbb{Q}$ is proper and geometrically connected. The conclusion asserts the existence of: a witness $h_{D\mathbb{Q}}$ that $D_0 \times_{R_p} \mathbb{Q}$ represents the corresponding rigidified $\mathrm{Pic}^0$ cut of the generic fibre of $c$, rigidified along the base-changed section; a morphism $\mathrm{aj}_{\mathbb{Q}}$ over $\mathbb{Q}$ from the generic fibre of $c$ to that of $D_0$; a morphism $k_{\mathbb{Q}}$ from the $\overline{\mathbb{Q}}$-fibre of $c$ (along `genPt p`) to its $\mathbb{Q}$-fibre; a morphism $\overline{\mathrm{aj}}$ from $\mathrm{Meta}_0.C$ to $D_0.P$; a $\overline{\mathbb{Q}}$-point $\bar\varepsilon$ of $\mathrm{Meta}_0.C$ over the identity; and a bijection $\mathrm{pts}$ from $J_{H'}(M/p) = \mathrm{Pic}^0(\overline{\mathbb{Q}}\cdot F(\Gamma_{H'}(M/p)))$ onto the $\overline{\mathbb{Q}}$-points of $D_0.\mathrm{toBase}$; subject to: the Poincaré bundle of $h_{D\mathbb{Q}}$ is isomorphic to the base-change transport of the pullback of the Poincaré bundle of $h_{D_0}$ along the first projection; the base-changed section composed with $\mathrm{aj}_{\mathbb{Q}}$ is the zero section; for every field $K$, every morphism $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of the generic fibre, the pullback of the Poincaré bundle along $x$ followed by $\mathrm{aj}_{\mathbb{Q}}$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of $t$ followed by the rigidifying section; $k_{\mathbb{Q}}$ commutes with the first projections and, on second projections, is $\operatorname{Spec}$ of $\mathbb{Q} \to \overline{\mathbb{Q}}$; $\overline{\mathrm{aj}} = e_0$ followed by $k_{\mathbb{Q}}$, $\mathrm{aj}_{\mathbb{Q}}$ and the first projection; $\overline{\mathrm{aj}}$ over the base equals $\mathrm{Meta}_0.\mathrm{toBase}$ followed by `genPt p`; $\bar\varepsilon$ lies over the cusp section $\varepsilon_\infty$ followed by $\pi$ and is sent by $\overline{\mathrm{aj}}$ to the zero section; $\mathrm{pts}$ is additive for the relative group law attached to $h_{D_0}$ through the fibrewise-algebraically-trivial group cut; and for all $\overline{\mathbb{Q}}$-points $x, s$ of $\mathrm{Meta}_0.C$ with $s$ lying over the cusp section, there is a degree-zero divisor $D_v$ equal to $[\,\text{place of } x\,] - [\,\text{place of } s\,]$ under the point–place bijection of $\mathrm{Meta}_0$, with $\mathrm{pts}$ of its class equal to $x$ followed by $\overline{\mathrm{aj}}$.
--
--   This transports the representability of the relative $\mathrm{Pic}^0$ of the level-$\Gamma_N(p,M,H)$ integral model to its generic fibre, equips it with an Abel–Jacobi morphism normalised at the cusp, and pins down, through an external curve model of $\overline{\mathbb{Q}}\cdot F(\Gamma_{H'}(M/p))$, a bijection between the degree-zero divisor class group of that function field and the $\overline{\mathbb{Q}}$-points of the representing scheme, compatible with the relative group law and with the classes $[x]-[s]$. It supplies the points dictionary and the Abel–Jacobi data used in the construction of the level-$M/p$ Néron object for $J_H$ and in the computation of the kernel of multiplication on its special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_XH
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓN p M H hpM) hj)]

    [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)]
    [GeometricallyIntegral (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)]

    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)
    (hsm₀ : Smooth D₀.toBase)

    (hprQ₀ : IsProper (pullback.snd D₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))))
    (hgcQ₀ : GeometricallyConnected (pullback.snd D₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))) :
    ∃ (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))) (D₀.baseChange ℚ))
      (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (D₀.baseChange ℚ).toBase)
      (kQ : pullback (toBase p (ΓN p M H hpM) hj) (genPt p) ⟶ pullback (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ))
      (ajbar : Meta₀.C ⟶ D₀.P)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _})
      (pts : JH (M / p) (infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) D₀.toBase),

      Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) ℚ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1 ≫ ajQ.1 = (D₀.baseChange ℚ).zeroSection ∧
      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (t ≫ (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      kQ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) ∧
      kQ ≫ pullback.snd (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧

      ajbar = eeta₀ ≫ kQ ≫ ajQ.1 ≫ pullback.fst D₀.toBase (specMap (R p) ℚ) ∧
      ajbar ≫ D₀.toBase = Meta₀.toBase ≫ genPt p ∧
      εbar.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 ∧
      εbar.1 ≫ ajbar = genPt p ≫ D₀.zeroSection ∧

      (∀ x y : JH (M / p) (infSubgroup p M H hpM),
        pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (pts x) (pts y)) ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
        s.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
            Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) := by sorry

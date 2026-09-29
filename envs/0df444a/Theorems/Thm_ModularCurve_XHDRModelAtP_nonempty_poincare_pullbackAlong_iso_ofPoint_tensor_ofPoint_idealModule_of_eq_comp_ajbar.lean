-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
-- name    : ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/49c446cc-9afe-5570-bd64-6a0f9e3c577b
-- title:
--   Poincaré bundle at ℚ̄-points of the integral model
-- statement:
--   Fix a prime $p$, an integer $M\neq 0$ with $p\mid M$, a subgroup $H\le(\mathbb{Z}/M)^{\times}$, and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the function field `qExpFunctionFieldC ℚ ⊤`; let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, whose structure morphism $f=$ `toBase p (ΓM M H) hj` to $\operatorname{Spec}(R\,p)$ and whose base change $f_{\mathbb{Q}}$ to $\mathbb{Q}$ are assumed separated, and write $\varepsilon_\infty=\mathfrak{X}.\mathrm{εinf}$ for the distinguished section of $f$. Let $D$ be a `RelativePic0Designation` for $f$ (a scheme $D.P$ over $\operatorname{Spec}(R\,p)$ with a zero section), let `hD` witness that $D$ represents the functor of rigidified line bundles on $f$ with section $\varepsilon_\infty$ satisfying `algEquivZeroCut` (fibrewise algebraic equivalence to zero), with Poincaré bundle `hD.poincare`, and let `hDQ` be the corresponding witness for $f_{\mathbb{Q}}$, the base-changed section, and $D.\mathrm{baseChange}\ \mathbb{Q}$. Given further: a morphism $\mathrm{aj}_{\mathbb{Q}}$ from $\mathfrak{X}_{\mathbb{Q}}$ to $(D.\mathrm{baseChange}\ \mathbb{Q}).\mathrm{toBase}$ over $\operatorname{Spec}\mathbb{Q}$; a morphism $k_{\mathbb{Q}}$ from $\mathfrak{X}\times_{R\,p}\bar{\mathbb{Q}}$ to $\mathfrak{X}\times_{R\,p}\mathbb{Q}$ compatible with the first projections (`hkQ₁`) and inducing $\operatorname{Spec}\bar{\mathbb{Q}}\to\operatorname{Spec}\mathbb{Q}$ on the second (`hkQ₂`); a morphism $\overline{\mathrm{aj}}$ from $\mathfrak{X}.\mathrm{Meta}.C$ to $D.P$ equal to $\mathfrak{X}.\mathrm{eeta}$ followed by $k_{\mathbb{Q}}$, $\mathrm{aj}_{\mathbb{Q}}$ and the projection to $D.P$; an isomorphism `hPQ` between the underlying module of `hDQ.poincare` and the base change to $\mathbb{Q}$ of the pullback of `hD.poincare` along the first projection of $D.P\times_{R\,p}\mathbb{Q}$; and the classification hypothesis `hajcl`, that for every field $K$, every $t:\operatorname{Spec}K\to\operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of $\mathfrak{X}_{\mathbb{Q}}$ over $t$, the pullback of `hDQ.poincare` along $x$ followed by $\mathrm{aj}_{\mathbb{Q}}$ has underlying module isomorphic to the invertible dual of the graph ideal of $x$ tensored with the ideal module of the graph of $t$ followed by the base-changed cusp section. Then for every $\bar{\mathbb{Q}}$-point $y$ of $\mathfrak{X}.\mathrm{Meta}.C$ over $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$, every $\bar{\mathbb{Q}}$-point $\bar y$ of $\mathfrak{X}$ over `genPt p` with $\bar y=y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, and every $\bar{\mathbb{Q}}$-point $a$ of $D.P$ over `genPt p` with $a=y$ followed by $\overline{\mathrm{aj}}$, the module underlying the pullback of `hD.poincare` along $a$ is isomorphic to the line bundle (dual of the graph ideal) of the relative effective Cartier divisor of the point $\bar y$ tensored with the ideal module of the relative effective Cartier divisor of `genPt p` followed by $\varepsilon_\infty$.
--
--   This is the Abel–Jacobi classification of the Poincaré bundle, transported from the generic fibre to $\bar{\mathbb{Q}}$-points of the integral model of $X_H(M)$ at $p$: the fibre of the Poincaré bundle over the point $\overline{\mathrm{aj}}(y)$ of the relative $\mathrm{Pic}^0$ is $\mathcal{O}(\bar y - \varepsilon_\infty)$. It feeds the identification of points of the Néron object attached to $J_H$ with divisor classes, used in the computations of Galois and Hecke action on those points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ D.P)
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajcl : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (ybar : SchemeHomOver (genPt p) (toBase p (ΓM M H) hj))
    (hybar : ybar.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (a : SchemeHomOver (genPt p) D.toBase) (ha : a.1 = y.1 ≫ ajbar) :
    Nonempty ((hD.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar.1 ybar.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (genPt p ≫ 𝔛.εinf.1)
          ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔛.εinf.2).trans (Category.comp_id _)))).idealModule) := by sorry

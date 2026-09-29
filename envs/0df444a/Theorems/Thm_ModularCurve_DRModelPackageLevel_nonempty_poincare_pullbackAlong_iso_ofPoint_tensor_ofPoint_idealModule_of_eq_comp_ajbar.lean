-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
-- name    : ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/4f602d7a-5de0-56bc-9df5-03f2db983417
-- title:
--   Poincaré bundle at geometric Abel–Jacobi points equals 𝒪(̄ y-∞)
-- statement:
--   Fix a nonzero $N_0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀` for the Igusa scheme $\mathfrak{X} =$ `X N₀ p` with structure morphism $f =$ `toBase N₀ p` to $\operatorname{Spec}(R_p)$, assumed proper. Let $D$ be a `RelativePic0Designation` for $f$, i.e. a scheme $D.P$ over $\operatorname{Spec}(R_p)$ with a zero section, and let `hD` be the datum that $D$ represents the subfunctor of rigidified line bundles on $\mathfrak{X} \times_{R_p} T$ rigidified along $\mathfrak{P}.\varepsilon_\infty$ and fibrewise algebraically equivalent to zero: a Poincaré bundle on $\mathfrak{X} \times_{R_p} D.P$ in that class, unique classifying maps, and triviality along the zero section. Assume in addition: the analogous representability datum `hDQ` over $\mathbf{Q}$ for the base-changed designation $D \times_{R_p} \mathbf{Q}$; an isomorphism between its Poincaré bundle and the transport to $\mathbf{Q}$ of the pullback of `hD.poincare` along the first projection of $D.P \times_{R_p} \mathbf{Q}$; a morphism $aj_{\mathbf{Q}}$ from $\mathfrak{X}_{\mathbf{Q}}$ to $(D \times_{R_p} \mathbf{Q}).P$ over $\operatorname{Spec}\mathbf{Q}$ such that for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbf{Q}$ and every $K$-point $x$ of $\mathfrak{X}_{\mathbf{Q}}$ over $t$, the pullback of `hDQ.poincare` along $x$ followed by $aj_{\mathbf{Q}}$ is isomorphic to the dual of the ideal sheaf of the graph of $x$ tensored with the ideal sheaf of the graph of $t$ followed by the base-changed section $\varepsilon_\infty$; a morphism $k_{\mathbf{Q}}$ from $\mathfrak{X} \times_{R_p} \overline{\mathbf{Q}}$ to $\mathfrak{X} \times_{R_p} \mathbf{Q}$ compatible with the first projections and with the second projections up to $\operatorname{Spec}$ of $\mathbf{Q} \to \overline{\mathbf{Q}}$; and a morphism $\overline{aj}$ from $\mathfrak{P}.\mathrm{Meta}.C$ to $D.P$ equal to $\mathfrak{P}.\mathrm{eeta}$ followed by $k_{\mathbf{Q}}$, $aj_{\mathbf{Q}}$ and the first projection of $D.P \times_{R_p} \mathbf{Q}$. Then for every $\overline{\mathbf{Q}}$-point $y$ of $\mathfrak{P}.\mathrm{Meta}.C$ over its base, every $\overline{\mathbf{Q}}$-point $\bar y$ of $\mathfrak{X}$ over `genPt p` whose underlying morphism is $y$ followed by $\mathfrak{P}.\mathrm{eeta}$ and the first projection, and every point $a$ of $D.P$ over `genPt p` whose underlying morphism is $y$ followed by $\overline{aj}$, the pullback of `hD.poincare` along $a$ has underlying module isomorphic to the dual of the ideal sheaf of the graph of $\bar y$ tensored with the ideal sheaf of the graph of `genPt p` followed by $\mathfrak{P}.\varepsilon_\infty$, both taken on $\mathfrak{X} \times_{R_p} \overline{\mathbf{Q}}$.
--
--   This is the Abel–Jacobi classification property read at geometric points: on $\overline{\mathbf{Q}}$-points of the model curve, the geometric Abel–Jacobi morphism $\overline{aj}$ sends $y$ to the point of $D.P$ classifying $\mathcal{O}(\bar y - \infty)$ for the Poincaré bundle living at the level of $R_p = \mathbf{Z}_{(p)}$, rather than only over $\mathbf{Q}$. It is the form used by the comparisons of $\overline{aj}$ with the Atkin–Lehner involution and with the degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar.lean

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
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel
  ModularCurve.JZeroNeronObjectAtP AlgebraicCurve

theorem ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (ybar : SchemeHomOver (genPt p) (toBase N₀ p)) (hybar : ybar.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
    (a : SchemeHomOver (genPt p) D.toBase) (ha : a.1 = y.1 ≫ ajbar) :
    Nonempty ((hD.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint (toBase N₀ p) ybar.1 ybar.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1)
          ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔓.εinf.2).trans (Category.comp_id _)))).idealModule) := by sorry

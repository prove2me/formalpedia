-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic_abelJacobi_pts_of_representsRelSubPic
-- name    : ModularCurve.DRModelPackageLevel.exists_representsRelSubPic_abelJacobi_pts_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/7ddc9558-5e93-59f9-aa8e-557b95d418a4
-- title:
--   Points dictionary for the relative Pic⁰ of the level-N₀p model
-- statement:
--   Let $N_0$ be a nonzero natural number and $p$ a prime with $p\nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ p hpN₀`: a Deligne–Rapoport package for the Igusa scheme $\mathfrak X\to\operatorname{Spec}(R\,p)$ with structure morphism `toBase N₀ p`, comprising properness, flatness, integrality and finite presentation, normality on affine opens, a curve model $\mathfrak P.\mathrm{Meta}$ of the field `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbf Q}$ together with an isomorphism $\mathfrak P.\mathrm{eeta}$ onto the $\overline{\mathbf Q}$-fibre and its Galois compatibility, smoothness and geometric integrality of the $\mathbf Q$-fibre, and sections $\varepsilon_\infty,\varepsilon_0$ of `toBase N₀ p`. Let $D$ be a relative $\operatorname{Pic}^0$ designation over $R\,p$, that is, a scheme $D.P$ with a morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}(R\,p)$ and a zero section, and let $hD$ witness that $D$ represents the rigidified relative Picard functor of $(\mathfrak X,\varepsilon_\infty)$ restricted to the cut `algEquivZeroCut` of bundles whose geometric fibres are algebraically equivalent to zero: a Poincaré rigidified bundle in the cut, universality up to unique classifying map, and triviality along the zero section. Assume $D.\mathrm{toBase}$ smooth and its base change to $\mathbf Q$ proper and geometrically connected. Then there exist: a representing datum $h_{\mathbf Q}$ for the same cut for the base-changed curve $(\mathfrak X_{\mathbf Q},\varepsilon_{\infty,\mathbf Q})$ and designation $D_{\mathbf Q}=D.\mathrm{baseChange}\ \mathbf Q$; a morphism $aj_{\mathbf Q}\colon\mathfrak X_{\mathbf Q}\to D_{\mathbf Q}$ over $\operatorname{Spec}\mathbf Q$; a morphism $k_{\mathbf Q}$ from $\mathfrak X\times_{R\,p}\overline{\mathbf Q}$ to $\mathfrak X\times_{R\,p}\mathbf Q$; a morphism $\overline{aj}\colon\mathfrak P.\mathrm{Meta}.C\to D.P$; a $\overline{\mathbf Q}$-point $\bar\varepsilon$ of $\mathfrak P.\mathrm{Meta}.C$; and a bijection $\mathrm{pts}$ from `JZero (N₀ * p)`, the degree-zero divisor class group of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbf Q}$, onto the set of $\overline{\mathbf Q}$-points of $D$ over `genPt p`, such that: the Poincaré bundle of $h_{\mathbf Q}$ is isomorphic to the transport along `BaseChange.ofR` of the pullback of that of $hD$ along the first projection; $\varepsilon_{\infty,\mathbf Q}$ followed by $aj_{\mathbf Q}$ is the zero section of $D_{\mathbf Q}$; for every field $K$, every $t\colon\operatorname{Spec}K\to\operatorname{Spec}\mathbf Q$ and every $K$-point $x$ of $\mathfrak X_{\mathbf Q}$ over $t$, the pullback of the Poincaré bundle of $h_{\mathbf Q}$ along $x$ followed by $aj_{\mathbf Q}$ is isomorphic to the dual of the ideal sheaf module of the relative effective Cartier divisor of $x$ tensored with the ideal sheaf module of that of the cusp $t\circ\varepsilon_{\infty,\mathbf Q}$; $k_{\mathbf Q}$ commutes with the first projections and intertwines the second projections through $\operatorname{Spec}\overline{\mathbf Q}\to\operatorname{Spec}\mathbf Q$; $\overline{aj}$ equals $\mathfrak P.\mathrm{eeta}$ followed by $k_{\mathbf Q}$, $aj_{\mathbf Q}$ and the first projection, and lies over $\mathfrak P.\mathrm{Meta}.\mathrm{toBase}$ followed by `genPt p`; $\bar\varepsilon$ is carried by $\mathfrak P.\mathrm{eeta}$ and the first projection to the cusp $\varepsilon_\infty$, and $\bar\varepsilon$ followed by $\overline{aj}$ is the zero section; $\mathrm{pts}$ is additive for the relative group law on $D$ furnished by $hD$ through `algEquivZeroGroupCut`; $\mathrm{pts}(\sigma\cdot x)=\operatorname{Spec}(\sigma)$ followed by $\mathrm{pts}(x)$ for every $\sigma\in\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$; and for all $\overline{\mathbf Q}$-points $x,s$ of $\mathfrak P.\mathrm{Meta}.C$ with $s$ the cusp in the above sense, there is a degree-zero divisor equal to the difference of the places attached to $x$ and $s$ by $\mathfrak P.\mathrm{Meta}.\mathrm{pointEquivPlace}$ whose class is sent by $\mathrm{pts}$ to $x$ followed by $\overline{aj}$.
--
--   This is the transport of the relative $\operatorname{Pic}^0$ structure of the level-$N_0p$ Deligne–Rapoport model to its generic fibre, together with the Abel–Jacobi normalisation at the cusp and the resulting dictionary between $J_0(N_0p)(\overline{\mathbf Q})$, described as the degree-zero divisor class group of the modular function field, and the $\overline{\mathbf Q}$-points of the representing scheme. It supplies the `pts`, `pts_add`, `pts_galois` data and the Abel–Jacobi pin used in the construction of the Néron object at $p$ for $J_0(N_0p)$, and is cited by [`ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic_abelJacobi_pts_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.DRModelPackageLevel.exists_representsRelSubPic_abelJacobi_pts_of_representsRelSubPic
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (hsm : Smooth D.toBase)

    (hprQ : IsProper (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))))
    (hgcQ : GeometricallyConnected (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))) :
    ∃ (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
      (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
      (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
      (ajbar : 𝔓.Meta.C ⟶ D.P)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase),

      Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection ∧
      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p) ∧
      kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧

      ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ) ∧
      ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p ∧
      εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 ∧
      εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection ∧

      (∀ x y : JZero (N₀ * p),
        pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y)) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
          (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
            Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) := by sorry

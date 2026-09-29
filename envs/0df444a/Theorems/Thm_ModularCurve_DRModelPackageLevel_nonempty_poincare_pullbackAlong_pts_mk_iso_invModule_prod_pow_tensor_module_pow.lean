-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow
-- name    : ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/5d8ebb7d-b2c7-55e1-9574-ea22b0cb61f5
-- title:
--   Poincaré pullback at an effective divisor class as ideal-power modules
-- statement:
--   Fix a prime $p$ and $N_0\ge 1$ with $p\nmid N_0$, and let $\mathfrak P$ be a Deligne–Rapoport model package of level $N_0p$ over $R(p)$ for the Igusa structure morphism $\pi=$ `toBase N₀ p`, assumed proper. Let $D$ be a relative $\mathrm{Pic}^0$ designation over $R(p)$ (a scheme with structure morphism to $\operatorname{Spec}R(p)$ and a zero section), $hD$ a datum exhibiting $D$, via a rigidified Poincaré bundle, as representing the rigidified line bundles on $\pi$ rigidified along the cusp section $\mathfrak P.\varepsilon_\infty$ that are fibrewise algebraically equivalent to zero, and $hDQ$ the analogous datum after base change to $\mathbb Q$, together with an isomorphism $hPQ$ identifying the $\mathbb Q$-Poincaré bundle with the descent of the pullback of the $R(p)$-one along the first projection. Assume given an Abel–Jacobi morphism $ajQ$ from the $\mathbb Q$-fibre of $\pi$ to $D_{\mathbb Q}$ sending the cusp section to the zero section, whose pullback of the $\mathbb Q$-Poincaré bundle along any $K$-point $x$ over $\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ is isomorphic to the dual of the ideal of the graph of $x$ tensored with the ideal module of the graph of the cusp; a comparison morphism $kQ$ from the $\overline{\mathbb Q}$-fibre to the $\mathbb Q$-fibre compatible with both projections (the second up to $\mathbb Q\to\overline{\mathbb Q}$); the induced morphism $ajbar$ from $\mathfrak P.\mathrm{Meta}.C$ to $D.P$ over $\overline{\mathbb Q}$, defined as $\mathfrak P.\mathrm{eeta}$ followed by $kQ$, $ajQ$ and the first projection; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak P.\mathrm{Meta}.C$ lying over the cusp and sent by $ajbar$ to the zero section; and a bijection $\mathrm{pts}$ from $J_0(N_0p)=\mathrm{Pic}^0(\overline{\mathbb Q}(X_0(N_0p)))$ onto the $\overline{\mathbb Q}$-points of $D$ which is additive for the relative group law supplied by $hD$, Galois-equivariant, and normalised so that for $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak P.\mathrm{Meta}.C$ with $s$ over the cusp there is a degree-zero divisor equal to $[\,\text{place of }x\,]-[\,\text{place of }s\,]$ whose class is carried by $\mathrm{pts}$ to $x$ followed by $ajbar$. Finally let $s$ be a finite set of places of $\overline{\mathbb Q}(X_0(N_0p))$ with multiplicities $m_w\in\mathbb N$, let $\bar y_w$ be the $\overline{\mathbb Q}$-points of $\pi$ obtained from the places through $\mathfrak P.\mathrm{Meta}$ and $\mathfrak P.\mathrm{eeta}$, and let $D_v$ be a degree-zero divisor with $D_v=\sum_{w\in s}m_w[w]-\bigl(\sum_{w\in s}m_w\bigr)[\,\text{place of }\bar\varepsilon\,]$. Then the pullback of the Poincaré bundle along $\mathrm{pts}$ of the class of $D_v$ is isomorphic, as a module on the $\overline{\mathbb Q}$-fibre of $\pi$, to the dual of $\prod_{w\in s}\mathfrak a_{\bar y_w}^{m_w}$ tensored with $\mathfrak a_{\bar\infty}^{\sum_{w\in s}m_w}$ viewed as a module, where $\mathfrak a_q$ denotes the ideal sheaf of the graph of the point $q$ and $\bar\infty$ is the $\overline{\mathbb Q}$-point of the cusp.
--
--   This is the Abel–Jacobi dictionary for the Poincaré bundle extended from single $\overline{\mathbb Q}$-points to arbitrary effective divisors supported on finitely many places, the one-point case being `nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar`. It is used in the identification of the action of degeneracy and Hecke operators on $J_0(N_0p)$ with morphisms of the relative $\mathrm{Pic}^0$ model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow.lean

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
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel
  ModularCurve.JZeroNeronObjectAtP AlgebraicCurve

theorem ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
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
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (s : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))))
    (m : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) → ℕ)
    (ybar : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) → SchemeHomOver (genPt p) (toBase N₀ p))
    (hybar : ∀ w, (ybar w).1 = (𝔓.Meta.pointEquivPlace.symm w).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
    (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      ∑ w ∈ s, (m w : ℤ) • Finsupp.single w 1 -
        ((∑ w ∈ s, m w : ℕ) : ℤ) • Finsupp.single (𝔓.Meta.pointEquivPlace εbar) 1) :
    Nonempty ((hD.poincare.pullbackAlong (pts (Pic0.mk Dv))).L ≅
      (∏ w ∈ s, (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I ^ m w).invModule ⊗
        ((RelEffCartierDiv.ofPoint (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1)
            ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔓.εinf.2).trans (Category.comp_id _)))).I ^
          (∑ w ∈ s, m w)).module) := by sorry

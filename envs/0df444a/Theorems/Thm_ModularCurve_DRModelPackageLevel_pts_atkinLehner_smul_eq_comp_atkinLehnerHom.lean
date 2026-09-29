-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_pts_atkinLehner_smul_eq_comp_atkinLehnerHom
-- name    : ModularCurve.DRModelPackageLevel.pts_atkinLehner_smul_eq_comp_atkinLehnerHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/e9a5c58c-7160-5ee0-ab59-8202289dbb78
-- title:
--   Atkin–Lehner involution acts as w_* on ℚ̄-points
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$ with $p\nmid N_0$, and a level-$N_0p$ Deligne–Rapoport model package $\mathfrak P$ for the Igusa-type curve $X$ over $\operatorname{Spec}(R_p)$ with structural morphism `toBase N₀ p` assumed proper, cusp section $\varepsilon_\infty=\mathfrak P.\mathrm{εinf}$, involution $\mathfrak P.w$, and geometric model $\mathfrak P.\mathrm{Meta}$ of the field $\overline{\mathbf Q}(X_0(N_0p))$ = `modularFunctionFieldBar (N₀ * p)` together with the identification $\mathfrak P.\mathrm{eeta}$ of $\mathfrak P.\mathrm{Meta}.C$ with the geometric generic fibre. Assume: a designation $D$ (a scheme over $\operatorname{Spec}(R_p)$ with zero section) together with data $hD$ representing, with Poincaré bundle $hD.\mathrm{poincare}$, the sub-Picard condition of fibrewise algebraically trivial rigidified line bundles on $(X,\varepsilon_\infty)$; the corresponding representability $hDQ$ for the base change to $\mathbf Q$ together with an isomorphism $hPQ$ of its Poincaré bundle with the base change of $hD.\mathrm{poincare}$; a morphism $aj_{\mathbf Q}$ from the generic fibre to $D_{\mathbf Q}$ over $\mathbf Q$ sending the cusp to the zero section and classifying, on points with values in any field, the class $\mathcal O(x)\otimes\mathcal O(-\infty)$ (the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of that of the cusp); a comparison morphism $k_{\mathbf Q}$ from the fibre over the geometric generic point to the fibre over $\mathbf Q$, compatible with both projections up to $\operatorname{Spec}\overline{\mathbf Q}\to\operatorname{Spec}\mathbf Q$; the induced map $\overline{aj}=\mathfrak P.\mathrm{eeta}\circ$ (through $k_{\mathbf Q}$ and $aj_{\mathbf Q}$) lying over the geometric generic point, and a $\overline{\mathbf Q}$-point $\bar\varepsilon$ of $\mathfrak P.\mathrm{Meta}.C$ which is the cusp and is sent by $\overline{aj}$ to the zero section; a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0$ of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbf Q}$ to the $\overline{\mathbf Q}$-points of $D$ which is additive for the relative group law attached to $hD$, equivariant for $\operatorname{Aut}(\overline{\mathbf Q}/\mathbf Q)$, and normalised by $\overline{aj}$ in the sense that for all $\overline{\mathbf Q}$-points $x$ and cusp points $s$ the class of the divisor $(x)-(s)$ is sent to $x$ followed by $\overline{aj}$; finally an endomorphism $w_*$ of $D$ over $\operatorname{Spec}(R_p)$ which, on $T$-valued points $a$, classifies the pullback of $hD.\mathrm{poincare}$ along the curve change induced by $\mathfrak P.w$, re-rigidified along the cusp section, and which is a homomorphism for the relative group law. Then for every class $x$ in $\mathrm{Pic}^0$, the point $\mathrm{pts}$ of the image of $x$ under the action of the automorphism `geomAut` of `modularFunctionFieldBar (N₀ * p)` induced by `atkinLehnerInvolutionFull N₀ p` equals $\mathrm{pts}(x)$ followed by $w_*$.
--
--   This identifies the endomorphism $w_*$ of the relative $\mathrm{Pic}^0$ scheme, characterised by pullback of rigidified line bundles along the Atkin–Lehner involution of the Deligne–Rapoport model, with the Atkin–Lehner involution $w_p$ acting on $J_0(N_0p)(\overline{\mathbf Q})$ through transport of places along the automorphism of the level-$N_0p$ modular function field. It is used in the construction of the $U_p$ operator on $D$, in [`ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp`](thm.html#ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_pts_atkinLehner_smul_eq_comp_atkinLehnerHom.lean

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

theorem ModularCurve.DRModelPackageLevel.pts_atkinLehner_smul_eq_comp_atkinLehnerHom
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

    (wstar : SchemeHomOver D.toBase D.toBase)
    (hw : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a wstar)).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) t 𝔓.εinf) (pullback.snd (toBase N₀ p) t)
          ((Scheme.Modules.pullback (curveChange 𝔓.w.hom 𝔓.w_over t)).obj (hD.poincare.pullbackAlong a).L)))
    (hwhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) wstar =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t
          (NeronModelInfra.schemeHomOverComp x wstar) (NeronModelInfra.schemeHomOverComp y wstar)) :
    ∀ x : JZero (N₀ * p),
      (pts ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)) • x)).1 =
        (pts x).1 ≫ wstar.1 := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w
-- name    : ModularCurve.DRModelPackageLevel.mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/e945e6d3-42c4-5f18-bb3a-4ec12face3f3
-- title:
--   Atkin–Lehner endomorphism on Abel–Jacobi points of Pic⁰
-- statement:
--   Fix $N_0$ and a prime $p$ with $p \nmid N_0$, and a Deligne–Rapoport model package $\mathfrak P$ of level $N_0p$ at $p$, with `toBase N₀ p` proper. Let $D$ be a relative $\mathrm{Pic}^0$ designation over $R_p$ for that curve (a scheme with structure morphism and a zero section), and let $hD$ exhibit $D$ as representing the rigidified line bundles on the curve that are fibrewise algebraically equivalent to zero, with Poincaré bundle $hD.\mathrm{poincare}$; let $hDQ$ do the same after base change to $\mathbb Q$ for `D.baseChange ℚ`, the two Poincaré bundles being identified by $hPQ$. Assume given: a morphism $ajQ$ from the $\mathbb Q$-curve to $(D_{\mathbb Q})$ over $\operatorname{Spec}\mathbb Q$ sending the section $\varepsilon_\infty$ to the zero section, and classifying, on every point $x$ over a field, the line bundle $\mathcal O(x) \otimes \mathcal O(-\varepsilon_\infty)$; a morphism $kQ$ from the geometric generic fibre to the $\mathbb Q$-fibre compatible with both projections; the induced Abel–Jacobi morphism $\overline{aj}$ from $\mathfrak P.\mathrm{Meta}.C$ to $D.P$, factoring as $\mathfrak P.\mathrm{eeta}$, $kQ$, $ajQ$ and the first projection, lying over the generic point; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathrm{Meta}.C$ mapping to $\varepsilon_\infty$ and killed by $\overline{aj}$; a bijection $pts$ from $\mathrm{Pic}^0$ of the modular function field over $\overline{\mathbb Q}$ to the $\overline{\mathbb Q}$-points of $D$, additive for the group law of $hD$, Galois-equivariant, and compatible with $\overline{aj}$ in the sense that for points $x,s$ with $s$ over $\varepsilon_\infty$ the class of the divisor $[x]-[s]$ is sent to $x$ followed by $\overline{aj}$; and an endomorphism $w^\ast$ of $D$ over $R_p$ which classifies the pullback of the Poincaré bundle along the involution $\mathfrak P.w$, re-rigidified along the zero section, and is a homomorphism for the group law. Let $y,y',\varepsilon'$ be $\overline{\mathbb Q}$-points of $\mathrm{Meta}.C$ with $\mathfrak P.w$ carrying $y'$ to $y$ and $\varepsilon'$ to $\bar\varepsilon$, and let $a,b,c$ be the $\overline{\mathbb Q}$-points of $D$ given by $y$ followed by $\overline{aj}$ and then $w^\ast$, by $\varepsilon'$ followed by $\overline{aj}$, and by $y'$ followed by $\overline{aj}$. Then $a \cdot b = c$ for the relative group law attached to $hD$.
--
--   This is the pointwise compatibility of the Atkin–Lehner endomorphism $w^\ast$ of the Deligne–Rapoport $\mathrm{Pic}^0$ object with the Abel–Jacobi embedding: $w^\ast(\mathrm{aj}\,y) + \mathrm{aj}(\varepsilon') = \mathrm{aj}(y')$, reflecting $w^\ast(\mathcal O(y)-\mathcal O(\bar\varepsilon)) = \mathcal O(y')-\mathcal O(\varepsilon')$. It is used to identify the Atkin–Lehner action on $\mathrm{Pic}^0$ of the modular curve with composition by $w^\ast$ on $\overline{\mathbb Q}$-points of $D$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w.lean

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

theorem ModularCurve.DRModelPackageLevel.mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w
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
          (NeronModelInfra.schemeHomOverComp x wstar) (NeronModelInfra.schemeHomOverComp y wstar))

    (y y' ε' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hy' : y'.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
    (hε' : ε'.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom = εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))

    (a b c : SchemeHomOver (genPt p) D.toBase)
    (ha : a.1 = (y.1 ≫ ajbar) ≫ wstar.1) (hb : b.1 = ε'.1 ≫ ajbar) (hc : c.1 = y'.1 ≫ ajbar) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul (genPt p) a b = c := by sorry

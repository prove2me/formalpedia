-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_mul_degeneracyHom_one_ajbar_abelJacobi_eq
-- name    : ModularCurve.DRModelPackageLevel.mul_degeneracyHom_one_ajbar_abelJacobi_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/d844a9de-dfcd-5902-a43a-9b48d02da4a9
-- title:
--   Second degeneracy norm map versus Abel–Jacobi on ℚ̄-points
-- statement:
--   Fix $N_0$ and a prime $p$ with $p \nmid N_0$, and a level package $\mathfrak P$ of type `DRModelPackageLevel N₀ p hpN₀` with `toBase N₀ p` proper. Let $D$ be a relative $\mathrm{Pic}^0$ designation over $R(p)$ for `toBase N₀ p` (a scheme with structure morphism to $\operatorname{Spec} R(p)$ and a zero section), let `hD` exhibit $D$ as representing the sub-Picard condition "fibrewise algebraically equivalent to zero" for line bundles rigidified along $\mathfrak P.\varepsilon_{\infty}$, and let `hDQ` do the same for the base change of $D$ to $\mathbb Q$, with `hPQ` an isomorphism between the Poincaré bundle of `hDQ` and the descent-to-$\mathbb Q$ of the pullback of that of `hD` along the first projection. Let $\mathrm{aj}_{\mathbb Q}$ be a morphism from the curve over $\mathbb Q$ to the base of $D_{\mathbb Q}$ which sends the $\infty$-section to the zero section and which, for every point $x$ of the curve over a field-valued base $t$, classifies the line bundle of $x$ tensored with the ideal module of the $\infty$-section, and let $k_{\mathbb Q}$ be a comparison morphism from the fibre over the geometric generic point to the fibre over $\operatorname{Spec}\mathbb Q$, compatible with both projections. Put $\overline{\mathrm{aj}} = \mathfrak P.\mathrm{eeta} \,;\, k_{\mathbb Q} \,;\, \mathrm{aj}_{\mathbb Q} \,;\, \mathrm{pr}_1$, a morphism $\mathfrak P.\mathrm{Meta}.C \to D.P$ lying over `genPt p`, and let $\bar\varepsilon$ be a section of $\mathfrak P.\mathrm{Meta}.\mathrm{toBase}$ mapping to the $\infty$-section and satisfying $\bar\varepsilon \,;\, \overline{\mathrm{aj}} = \mathrm{genPt}(p) \,;\, D.\mathrm{zeroSection}$. Further data: a valuation subring $A$ of $\overline{\mathbb Q}$, a level model $M$ over $A$ whose associated level data is `IsJacobian`, the hypotheses that $\mathfrak P.\pi$ is finite, flat and locally of finite presentation of constant fibre rank $p+1$, and a pair $\delta : \mathrm{Fin}\,2 \to$ morphisms $D.\mathrm{toBase} \to M.D_0.\mathrm{toBase}$ over $\operatorname{Spec} R(p)$ of which $\delta_1$ is pinned by the norm condition: for every base $t$ and every $a$ over $t$ with values in $D.\mathrm{toBase}$, the pullback along $a \,;\, \delta_1$ of $M$'s Poincaré bundle is isomorphic to the rigidification, along the $\varepsilon_0$-section, of the degree-$(p+1)$ norm module of the pullback of `hD`'s Poincaré bundle along $a$, taken along the curve change induced by $\mathfrak P.\pi_w$. Finally let $y$ be a section of $\mathfrak P.\mathrm{Meta}.\mathrm{toBase}$ and $x, x_\infty$ sections of $M.\mathrm{Meta}_0.\mathrm{toBase}$ over $\operatorname{Spec}\overline{\mathbb Q}$ such that $x$ is the image of $y$ and $x_\infty$ the image of $\bar\varepsilon$ under $\mathfrak P.\pi_w$, and let $a$, $b$, $c$ be the $\overline{\mathbb Q}$-points of $M.D_0.\mathrm{toBase}$ given by $a = y \,;\, \overline{\mathrm{aj}} \,;\, \delta_1$, $b = x_\infty \,;\, \mathrm{aj}_0$ and $c = x \,;\, \mathrm{aj}_0$ (the latter two read through $M.\mathrm{eeta}_0$ and the first projection). Then $a \cdot b = c$ in the relative group law `M.law` attached to $M.\mathrm{rep}$, evaluated at `genPt p`.
--
--   This is the compatibility of the second degeneracy morphism $\delta_1$, characterised by a norm-of-line-bundles condition along $\mathfrak P.\pi_w$, with the Abel–Jacobi maps of the two modular curves on geometric generic points: $\delta_1$ sends the class of $y - \bar\varepsilon$ to the class of $\pi_w(y) - \pi_w(\bar\varepsilon)$. It is the counterpart of the corresponding statement for $\delta_0$ and feeds into [`ModularCurve.DRModelPackageLevel.pts_degeneracyPushforwardPair_eq_comp_degeneracyHom`](thm.html#ModularCurve.DRModelPackageLevel.pts_degeneracyPushforwardPair_eq_comp_degeneracyHom), where $\delta_0$ and $\delta_1$ are identified with the degeneracy pushforwards on $J_0(N_0p)(\overline{\mathbb Q})$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_mul_degeneracyHom_one_ajbar_abelJacobi_eq.lean

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

theorem ModularCurve.DRModelPackageLevel.mul_degeneracyHom_one_ajbar_abelJacobi_eq
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
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A) (hM : M.toLevelData.IsJacobian)

    [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1] (hrk : ∀ x, 𝔓.π.1.finrank x = p + 1)
    (δ : Fin 2 → SchemeHomOver D.toBase M.D₀.toBase)
    (hδ₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((M.rep.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t M.ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.πw.1 𝔓.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (x xinf : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _})
    (hyx : x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.πw.1)
    (hxinf : xinf.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.πw.1)

    (a b c : SchemeHomOver (genPt p) M.D₀.toBase)
    (ha : a.1 = (y.1 ≫ ajbar) ≫ (δ 1).1)
    (hb : b.1 = xinf.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1)
    (hc : c.1 = x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1) :
    M.law.mul (genPt p) a b = c := by sorry

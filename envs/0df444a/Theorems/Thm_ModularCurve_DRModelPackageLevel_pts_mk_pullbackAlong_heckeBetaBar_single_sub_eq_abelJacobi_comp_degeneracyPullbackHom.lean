-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_pts_mk_pullbackAlong_heckeBetaBar_single_sub_eq_abelJacobi_comp_degeneracyPullbackHom
-- name    : ModularCurve.DRModelPackageLevel.pts_mk_pullbackAlong_heckeBetaBar_single_sub_eq_abelJacobi_comp_degeneracyPullbackHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/b88cd875-680a-5618-8bbd-e777e089943a
-- title:
--   Conorm divisors map to aj₀ followed by β^∗
-- statement:
--   Fix $N_0$ and a prime $p$ with $p \nmid N_0$ and a Deligne–Rapoport model package $\mathfrak{P}$ of level $N_0p$ over $R_p$, with proper structure morphism `toBase N₀ p`. The data are: a relative $\mathrm{Pic}^0$ designation $D$ (a scheme over $\operatorname{Spec} R_p$ with a zero section) together with $h_D$ exhibiting $D$ as representing the functor of line bundles rigidified along $\mathfrak{P}.\varepsilon_{\infty}$ that are fibrewise algebraically equivalent to zero; the analogous representability $h_{D\mathbb{Q}}$ over $\mathbb{Q}$ for the base-changed curve and designation, with $h_{P\mathbb{Q}}$ identifying its Poincaré bundle with the base change of the pullback of $h_D$'s; an Abel–Jacobi morphism $\mathrm{aj}_{\mathbb{Q}}$ over $\mathbb{Q}$ killing the section and classifying $\mathcal{O}(x)\otimes\mathcal{I}(\varepsilon)$ at every point over every field; a comparison $k_{\mathbb{Q}}$ between the geometric generic fibre and the $\mathbb{Q}$-fibre; the resulting morphism $\overline{\mathrm{aj}}$ from $\mathfrak{P}.\mathrm{Meta}.C$ to $D.P$ over `genPt p`, with a base point $\bar\varepsilon$ above $\mathfrak{P}.\varepsilon_{\infty}$ sent to the zero section; a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0(\overline{\mathbb{Q}}, \text{modularFunctionFieldBar}(N_0p))$ to the $\overline{\mathbb{Q}}$-points of $D$ that is additive for the relative group law of $h_D$, Galois-equivariant, and pinned to $\overline{\mathrm{aj}}$ on differences $[x]-[s]$ of places for $s$ above $\mathfrak{P}.\varepsilon_{\infty}$; a valuation subring $A$ of $\overline{\mathbb{Q}}$ and a level-$N_0$ model $M$ whose associated level data is Jacobian; and $\beta^{\ast}$, a morphism $M.D_0 \to D$ over $\operatorname{Spec} R_p$ which classifies, at every point over every base, the re-rigidified pullback of $M$'s Poincaré bundle along the degeneracy morphism $\mathfrak{P}.\pi_w$, and which is a homomorphism for the two relative group laws. Assume further that every nonzero function of the level-$N_0p$ function field over $\overline{\mathbb{Q}}$ has a principal divisor of degree zero, and that the Hecke $\beta$-morphism `heckeBetaBar` on function fields is integral. Then for $\overline{\mathbb{Q}}$-points $x$, $s_0$ of $M.\mathrm{Meta}_0.C$ with $s_0$ lying above $M.\varepsilon_0$, and for any degree-zero divisor $E'$ equal to the conorm $\sum_{w \mid v} e(w\mid v)\,[w]$ of the place of $x$ minus that of the place of $s_0$, the point $\mathrm{pts}([E'])$ equals the composite of $x$ with $M.\mathrm{eeta}_0$, the first projection and $M.\mathrm{aj}_0$, followed by $\beta^{\ast}$.
--
--   This is the compatibility of the divisor-theoretic dictionary with the degeneracy map between the Jacobians of level $N_0$ and level $N_0p$: pulling back a difference of points along the $\beta$-degeneracy (the conorm of places) corresponds, on the representing objects, to applying the level-$N_0$ Abel–Jacobi morphism and then the classifying morphism $\beta^{\ast}$. It feeds the statement [`ModularCurve.DRModelPackageLevel.pts_degeneracyPullbackPair_one_mk_eq_abelJacobi_comp_degeneracyPullbackHom`](thm.html#ModularCurve.DRModelPackageLevel.pts_degeneracyPullbackPair_one_mk_eq_abelJacobi_comp_degeneracyPullbackHom), which packages the degeneracy morphism between the two Néron-model objects.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_pts_mk_pullbackAlong_heckeBetaBar_single_sub_eq_abelJacobi_comp_degeneracyPullbackHom.lean

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

theorem ModularCurve.DRModelPackageLevel.pts_mk_pullbackAlong_heckeBetaBar_single_sub_eq_abelJacobi_comp_degeneracyPullbackHom
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

    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A) (hM : M.toLevelData.IsJacobian)

    (βstar : SchemeHomOver M.D₀.toBase D.toBase)
    (hβ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t M.D₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b βstar)).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) t 𝔓.εinf) (pullback.snd (toBase N₀ p) t)
          ((Scheme.Modules.pullback (curveChange 𝔓.πw.1 𝔓.πw.2 t)).obj (M.rep.poincare.pullbackAlong b).L)))
    (hβhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t M.D₀.toBase),
      NeronModelInfra.schemeHomOverComp (M.law.mul t x y) βstar =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t
          (NeronModelInfra.schemeHomOverComp x βstar) (NeronModelInfra.schemeHomOverComp y βstar))

    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))]
    (hint : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)

    (x s₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _})
    (hs₀ : s₀.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) = genPt p ≫ M.ε₀.1)
    (E' : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)))
    (hE' : (E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N₀ p) hint
          (Finsupp.single (M.Meta₀.pointEquivPlace x) 1) -
        Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N₀ p) hint
          (Finsupp.single (M.Meta₀.pointEquivPlace s₀) 1)) :
    (pts (Pic0.mk E')).1 =
      (x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1) ≫ βstar.1 := by sorry

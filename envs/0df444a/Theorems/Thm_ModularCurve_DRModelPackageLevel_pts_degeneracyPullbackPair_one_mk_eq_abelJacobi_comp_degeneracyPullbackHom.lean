-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_pts_degeneracyPullbackPair_one_mk_eq_abelJacobi_comp_degeneracyPullbackHom
-- name    : ModularCurve.DRModelPackageLevel.pts_degeneracyPullbackPair_one_mk_eq_abelJacobi_comp_degeneracyPullbackHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/4f2e4ccf-29e0-5e27-bafc-dede0df968c3
-- title:
--   Second degeneracy pullback of [x]-[s₀] equals β^∗circaj₀
-- statement:
--   Fix $N_0$ and a prime $p$ with $p \nmid N_0$, and a Deligne–Rapoport model package $\mathfrak P$ of level $N_0p$ over the base ring `R p`, the structure morphism `toBase N₀ p` being assumed proper. Let $D$ be a relative $\mathrm{Pic}^0$ designation for `toBase N₀ p` (a scheme over $\operatorname{Spec}(R\,p)$ with a zero section) and let `hD` exhibit $D$ as representing the subfunctor, of line bundles rigidified along $\mathfrak P.\varepsilon_{\inf}$, cut out by fibrewise algebraic triviality. The further data, summarised here, consist of: the analogous representability `hDQ` after base change to $\mathbb Q$ and an identification `hPQ` of its Poincaré bundle with the base change of that of `hD`; an Abel–Jacobi morphism $\mathrm{aj}_{\mathbb Q}$ over $\mathbb Q$ sending the rigidifying section to the zero section and classifying, on points $x$ over any field, the line bundle of the relative Cartier divisor of $x$ tensored with the ideal module of the divisor of the section; a comparison morphism $k_{\mathbb Q}$ from the fibre over the geometric generic point to the fibre over $\mathbb Q$, with its two projection identities; the induced geometric Abel–Jacobi morphism $\overline{\mathrm{aj}} = \mathfrak P.\mathrm{eeta} \;;\; k_{\mathbb Q}\;;\;\mathrm{aj}_{\mathbb Q}\;;\;\mathrm{pr}_1$, lying over `genPt p`, together with a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak P.\mathrm{Meta}.C$ lying over $\mathfrak P.\varepsilon_{\inf}$ and sent by $\overline{\mathrm{aj}}$ to the zero section; a bijection `pts` from $\mathrm{Pic}^0$ of the level-$N_0p$ modular function field over $\overline{\mathbb Q}$ onto the points of $D$ over `genPt p`, which is additive for the relative group law attached to `hD`, Galois-equivariant, and normalised so that for $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak P.\mathrm{Meta}.C$ with $s$ over $\mathfrak P.\varepsilon_{\inf}$ the class of $[\,\mathrm{place}(x)\,]-[\,\mathrm{place}(s)\,]$ is sent to $x \;;\;\overline{\mathrm{aj}}$; a valuation subring $A$ of $\overline{\mathbb Q}$ and a level-$N_0$ model $M$ over $A$ whose associated level data is Jacobian; and a morphism $\beta^\ast$ from $M.D_0$ to $D$ over $\operatorname{Spec}(R\,p)$ which classifies the re-rigidified pullback of $M$'s Poincaré bundle along the degeneracy curve change given by $\mathfrak P.\pi_w$ and is a homomorphism for the two relative group laws. Finally let $x, s_0$ be $\overline{\mathbb Q}$-points of $M.\mathrm{Meta}_0.C$ with $s_0$ lying over $M.\varepsilon_0$, and let $E$ be the degree-zero divisor $[\,\mathrm{place}(x)\,]-[\,\mathrm{place}(s_0)\,]$ on the level-$N_0$ function field. The conclusion is an equality of scheme morphisms: the point `pts` assigns to the image of the class of $E$ under the index-$1$ component of `degeneracyPullbackPair N₀ p` equals $x$ transported through $M.\mathrm{eeta}_0$ and the first projection to the level-$N_0$ curve, followed by $M.\mathrm{aj}_0$ and then by $\beta^\ast$.
--
--   This is the Abel–Jacobi compatibility on divisor classes of the shape $[x]-[s_0]$ for the second degeneracy pullback map $\mathrm{Pic}^0(X_0(N_0)) \to \mathrm{Pic}^0(X_0(N_0p))$, identifying its effect, read through the points dictionary of the level-$N_0p$ relative $\mathrm{Pic}^0$ object, with composition of the level-$N_0$ Abel–Jacobi morphism with $\beta^\ast$. Since such classes generate, it is the base case used by [`ModularCurve.DRModelPackageLevel.pts_degeneracyPullbackPair_one_eq_comp_degeneracyPullbackHom`](thm.html#ModularCurve.DRModelPackageLevel.pts_degeneracyPullbackPair_one_eq_comp_degeneracyPullbackHom), which extends the identity to all classes by additivity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_pts_degeneracyPullbackPair_one_mk_eq_abelJacobi_comp_degeneracyPullbackHom.lean

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

theorem ModularCurve.DRModelPackageLevel.pts_degeneracyPullbackPair_one_mk_eq_abelJacobi_comp_degeneracyPullbackHom
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

    (x s₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _})
    (hs₀ : s₀.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) = genPt p ≫ M.ε₀.1)
    (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N₀))
    (hE : (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀)) =
      Finsupp.single (M.Meta₀.pointEquivPlace x) 1 - Finsupp.single (M.Meta₀.pointEquivPlace s₀) 1) :
    (pts (degeneracyPullbackPair N₀ p 1 (Pic0.mk E))).1 =
      (x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1) ≫ βstar.1 := by sorry

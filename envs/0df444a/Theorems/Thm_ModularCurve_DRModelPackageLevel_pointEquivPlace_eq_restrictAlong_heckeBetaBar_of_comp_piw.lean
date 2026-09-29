-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw
-- name    : ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/db758ad6-003c-5da2-afe6-c7bd7a9e6fd1
-- title:
--   Second degeneracy morphism: places restrict along `heckeBetaBar`
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$, $p$ prime and $p \nmid N_0$, a Deligne–Rapoport model package $\mathfrak{P}$ of type `DRModelPackageLevel N₀ p hpN₀` for the Igusa scheme $X$ of level $N_0p$ over $\mathbf{Z}_{(p)}$, a valuation subring $A$ of $\overline{\mathbf{Q}}$ and a level datum $M$ of type `LevelModel N₀ p A` at level $N_0$; assume `hint`, that the $\overline{\mathbf{Q}}$-algebra homomorphism `heckeBetaBar` from the geometric modular function field of level $N_0$ to that of level $N_0p$ is integral as a ring homomorphism. The package supplies a curve model $\mathfrak{P}.\mathrm{Meta}$ of the geometric function field of level $N_0p$ together with an isomorphism $\mathfrak{P}.\mathrm{eeta}$ onto the pullback of `toBase N₀ p` along the geometric generic point `genPt p`, and a morphism $\mathfrak{P}.\pi w$ over the base from the level-$N_0p$ Igusa scheme to the level-$N_0$ one; $M$ supplies likewise a curve model $M.\mathrm{Meta}_0$ of the geometric function field of level $N_0$ with an isomorphism $M.\mathrm{eeta}_0$ onto the pullback of `IgusaScheme.igusaTo N₀ p` along `genPt p`. Let $y$ be a section of $\mathfrak{P}.\mathrm{Meta}.\mathrm{toBase}$ and $x$ a section of $M.\mathrm{Meta}_0.\mathrm{toBase}$ over $\operatorname{Spec} \overline{\mathbf{Q}}$, and suppose that $x$ followed by $M.\mathrm{eeta}_0$ and the first projection agrees with $y$ followed by $\mathfrak{P}.\mathrm{eeta}$, the first projection and $\mathfrak{P}.\pi w$. Then the place of the level-$N_0$ geometric function field attached to $x$ under the bijection `CurveModel.pointEquivPlace` between $\overline{\mathbf{Q}}$-sections and places equals the restriction along `heckeBetaBar` (`Place.restrictAlong`, i.e. restriction of the valuation under the algebra structure given by that homomorphism) of the place attached to $y$.
--
--   This is the place-theoretic description of the composite of the Atkin–Lehner involution with the degeneracy morphism from level $N_0p$ to level $N_0$: on $\overline{\mathbf{Q}}$-points it induces restriction of places along the second degeneracy embedding $\beta$ of modular function fields. It is used in identifying the second norm (pushforward) homomorphism between Jacobians of $X_0(N_0p)$ and $X_0(N_0)$, and is cited in the comparison of special fibres and of the two degeneracy pushforwards.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw.lean

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
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_AlgebraicCurve_Correspondence
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

theorem ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A)
    (hint : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _})
    (hyx : x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.πw.1) :
    M.Meta₀.pointEquivPlace x =
      (𝔓.Meta.pointEquivPlace y).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N₀ p) hint := by sorry

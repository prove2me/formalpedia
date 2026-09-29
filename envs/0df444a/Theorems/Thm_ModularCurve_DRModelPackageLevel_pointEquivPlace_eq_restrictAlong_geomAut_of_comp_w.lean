-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w
-- name    : ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/2cd31d83-007a-53bc-b665-0cecd3bfcc7e
-- title:
--   Atkin–Lehner involution restricts places along the geometric automorphism
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a term of `DRModelPackageLevel N₀ p hpN₀`: a Deligne–Rapoport style package for level $N_0p$ over the base `base p`, which among its data carries a curve model $\mathfrak{P}.\mathrm{Meta}$ of the field `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb{Q}}$ (a smooth proper integral $\overline{\mathbb{Q}}$-curve together with an identification of its function field, a bijection of its closed points with the places of that field, and pinning data), an isomorphism $\mathfrak{P}.\mathrm{eeta}$ of $\mathfrak{P}.\mathrm{Meta}.C$ with the geometric fibre `pullback (toBase N₀ p) (genPt p)`, and an isomorphism $\mathfrak{P}.w$ of the model $X(N_0,p)$ with itself. Write $\sigma$ for the $\overline{\mathbb{Q}}$-algebra automorphism `geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)`, obtained by base change to $\overline{\mathbb{Q}}$ of the chosen $\mathbb{Q}$-automorphism of `modularFunctionFieldFull (N₀ * p)` satisfying the Atkin–Lehner condition `IsAtkinLehnerAutFull N₀ p` (the identity if no such automorphism exists), and assume the hypothesis `hint` that the ring homomorphism underlying $\sigma$ is integral. Let $x,y$ be $\overline{\mathbb{Q}}$-points of $\mathfrak{P}.\mathrm{Meta}.C$, i.e. sections $q$ of $\mathfrak{P}.\mathrm{Meta}.\mathrm{toBase}$, and suppose that $x$ followed by $\mathfrak{P}.\mathrm{eeta}$ and the first projection to $X(N_0,p)$ equals $y$ followed by $\mathfrak{P}.\mathrm{eeta}$, that projection, and $\mathfrak{P}.w$. Then the place of `modularFunctionFieldBar (N₀ * p)` attached to $x$ by the bijection $\mathfrak{P}.\mathrm{Meta}.\mathrm{pointEquivPlace}$ is the restriction along $\sigma$ (the pullback of the valuation subring under $\sigma$, via the algebra structure induced by $\sigma$) of the place attached to $y$.
--
--   This identifies the action of the Atkin–Lehner involution of the integral model on geometric points of the generic fibre with the Atkin–Lehner automorphism of the function field acting on places. It is used in [`ModularCurve.DRModelPackageLevel.pts_atkinLehner_smul_eq_comp_atkinLehnerHom`](thm.html#ModularCurve.DRModelPackageLevel.pts_atkinLehner_smul_eq_comp_atkinLehnerHom) to read the Atkin–Lehner endomorphism of $J_0(N_0p)$ off the $\overline{\mathbb{Q}}$-points of the representing scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w.lean

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
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel
  ModularCurve.JZeroNeronObjectAtP AlgebraicCurve
open Topology
open scoped TensorProduct

theorem ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (hint : ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p))
      (atkinLehnerInvolutionFull N₀ p)).toAlgHom).toRingHom.IsIntegral)

    (y x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hyx : x.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) =
      y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom) :
    𝔓.Meta.pointEquivPlace x =
      (𝔓.Meta.pointEquivPlace y).restrictAlong
        (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)).toAlgHom hint := by sorry

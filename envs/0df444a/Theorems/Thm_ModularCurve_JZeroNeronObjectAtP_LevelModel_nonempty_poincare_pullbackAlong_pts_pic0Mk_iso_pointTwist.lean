-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
-- name    : ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/6988145d-bed3-54d0-aba4-4da2c6d234d9
-- title:
--   Poincaré pullback at a degree-zero class is the point twist
-- statement:
--   Fix $N_0$ nonzero and a prime $p$, a valuation subring $A$ of $\overline{\mathbf Q}$, and a level model $M$ of type `LevelModel N₀ p A`, so that $M$ carries the Igusa model `toBase0 N₀ p` $: X_0(N_0)\to\operatorname{Spec} \mathbf Z_{(p)}$ (here the base ring is the subring of $\mathbf Q$ of rationals with denominator coprime to $p$), a relative $\mathrm{Pic}^0$ designation $D_0$ with rigidified Poincaré bundle `M.rep.poincare`, a bijection `M.pts` from $\mathrm{Pic}^0(\overline{\mathbf Q}, \mathrm{modularFunctionFieldBar}\,N_0)$ to the sections of $D_0$ over the geometric generic point `genPt p`, and a curve model $M.\mathrm{Meta}_0$ of that function field together with an isomorphism $M.\mathrm{eeta}_0$ onto the fibre of $X_0(N_0)$ over `genPt p`; `toBase0 N₀ p` is assumed proper. The hypothesis `hJ` asserts that the level data of $M$ is a Jacobian: the conditions (an abelian-scheme property bundle, commutativity of the group law, additivity and Galois equivariance of `pts`, additivity of `ptsSp`, agreement of reduction of points modulo $\ell$ when the relevant inputs are given, and realisation of the Hecke algebra by endomorphisms compatible with the group law) are summarised here. Given $n$ sections $q_i$ of $M.\mathrm{Meta}_0$ over $\overline{\mathbf Q}$, $\overline{\mathbf Q}$-points $x_i$ of $X_0(N_0)$ over `genPt p` with $x_i$ the image of $q_i$ under $M.\mathrm{eeta}_0$ followed by the first projection, natural numbers $\mathrm{pos}_i,\mathrm{neg}_i$ with $\sum_i(\mathrm{pos}_i-\mathrm{neg}_i)=0$, and a degree-zero divisor $D_x$ equal to $\sum_i (\mathrm{pos}_i-\mathrm{neg}_i)$ times the place attached to $q_i$ under `M.Meta₀.pointEquivPlace`, the conclusion is that the pullback of the Poincaré bundle along the section `M.pts (Pic0.mk Dx)` has underlying module isomorphic to the right-nested tensor product, over $i=0,\dots,n-1$ and ending in the tensor unit of the category of modules on the fibre, of the dual of the module of the $\mathrm{pos}_i$-th power of the ideal sheaf of the graph divisor `RelEffCartierDiv.ofPoint` at $x_i$ tensored with the module of its $\mathrm{neg}_i$-th power; that is, $\bigotimes_i \mathcal O(\mathrm{pos}_i x_i)\otimes\mathcal O(-\mathrm{neg}_i x_i)$.
--
--   This is the compatibility of the Abel–Jacobi dictionary with divisor twists at level $N_0$: the Poincaré bundle restricted along the point of $\mathrm{Pic}^0$ attached to a degree-zero divisor $\sum_i m_i[q_i]$ is the corresponding twist of the trivial bundle by the points $x_i$, with the divisor at the rigidifying section cancelling because the total degree is zero. It is used in the comparison of special fibres of points, via [`ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization`](thm.html#ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) (hJ : M.toLevelData.IsJacobian) [IsProper (toBase0 N₀ p)]
    {n : ℕ} (q : Fin n → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _})
    (x : Fin n → SchemeHomOver (genPt p) (toBase0 N₀ p))
    (hxq : ∀ i, (x i).1 = (q i).1 ≫ M.eeta₀ ≫ pullback.fst (toBase0 N₀ p) (genPt p))
    (pos neg : Fin n → ℕ) (hn : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0)
    (Dx : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N₀))))
    (hDx : (Dx : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀)) =
      ∑ i, Finsupp.single (M.Meta₀.pointEquivPlace (q i)) ((pos i : ℤ) - (neg i : ℤ))) :
    Nonempty ((M.rep.poincare.pullbackAlong (M.pts (Pic0.mk Dx))).L ≅
      ((List.finRange n).foldr
          (fun i N => ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (x i).1 (x i).2).I ^ (pos i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (x i).1 (x i).2).I ^ (neg i)).module ⊗ N)
          (𝟙_ (pullback (toBase0 N₀ p) (genPt p)).Modules))) := by sorry

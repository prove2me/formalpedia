-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_ptsSp_symm_schemeHomOverComp_resPt_eq_reductionModL
-- name    : ModularCurve.JZeroNeronObjectAtP.LevelModel.ptsSp_symm_schemeHomOverComp_resPt_eq_reductionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/7a2ab797-1e8b-5b9a-b8c7-e243af6ad936
-- title:
--   Special fibre of an A-point equals reduction mod λ
-- statement:
--   Let $N_0$ and $p$ be natural numbers with $N_0 \neq 0$ and $p$ prime, and assume $p \nmid N_0$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ lying over $p$, meaning that $p$ is a non-unit of $A$, and let $M$ be a `LevelModel N₀ p A`: a package consisting of a ring homomorphism $\rho$ from the base ring at $p$ into $A$ compatible with the structure map to $\overline{\mathbf{Q}}$, a cusp section and chart data for the Igusa scheme of level $N_0$ at $p$, a relative $\mathrm{Pic}^0$ designation $D_0$ with its Abel–Jacobi datum, together with bijections $\mathrm{pts}$ from $\mathrm{JZero}\,N_0$ onto the sections of $D_0$ over the generic point and $\mathrm{ptsSp}$ from $\mathrm{JZeroC}(\kappa_A)\,N_0$ onto the sections of $D_0$ over $\operatorname{Spec}\kappa_A \to \operatorname{Spec} A$ (the residue point composed with $\operatorname{Spec}\rho$). Assume the predicate `IsJacobian` for the level datum attached to $M$, that is, the conjunction of the abelian-scheme property bundle for $D_0 \to$ base, commutativity of the relative group law, additivity of $\mathrm{pts}$ and of $\mathrm{ptsSp}$, Galois equivariance of $\mathrm{pts}$, the clause asserting agreement of reduction of points whenever `ReductionInputsModL` holds, and the Hecke clause. Let $x_0 \in \mathrm{JZero}\,N_0$ and let $b$ be a section of $D_0$ over $\operatorname{Spec}\rho$, i.e. a morphism $\operatorname{Spec} A \to D_0$ lying over $\operatorname{Spec}\rho$, whose restriction along $\operatorname{Spec}(A \hookrightarrow \overline{\mathbf{Q}})$ is $\mathrm{pts}(x_0)$. Then the inverse image under $\mathrm{ptsSp}$ of the restriction of $b$ along the residue point of $A$ equals $\mathrm{reductionModL}\,A\,N_0\,x_0$, the reduction of $x_0$ along the residue map of $A$.
--
--   This identifies the special fibre of an $A$-valued point of the level-$N_0$ Jacobian model in terms of the Deuring-style reduction map on degree-zero divisor classes: an $A$-point whose generic fibre is $\mathrm{pts}(x_0)$ has special fibre $\mathrm{ptsSp}$ of the reduction of $x_0$. It serves as the coordinate computation behind the comparison of Frobenius on the special fibre with the reduction map, and behind the corresponding statement for the level packages at a prime $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_ptsSp_symm_schemeHomOverComp_resPt_eq_reductionModL.lean

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

theorem ModularCurve.JZeroNeronObjectAtP.LevelModel.ptsSp_symm_schemeHomOverComp_resPt_eq_reductionModL
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) (hJ : M.toLevelData.IsJacobian)
    (x₀ : JZero N₀) (b : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) M.D₀.toBase)
    (hb : barPt A ≫ b.1 = (M.pts x₀).1) :
    M.toLevelData.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (JZeroNeronObjectAtP.resPt A) rfl b) = reductionModL A N₀ x₀ := by sorry

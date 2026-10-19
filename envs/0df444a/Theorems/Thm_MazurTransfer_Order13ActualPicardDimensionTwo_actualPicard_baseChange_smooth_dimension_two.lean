-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardDimensionTwo_actualPicard_baseChange_smooth_dimension_two
-- name    : MazurTransfer.Order13ActualPicardDimensionTwo.actualPicard_baseChange_smooth_dimension_two
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T09:32:13.332637+00:00
-- url     : https://prove2.me/theorems/22a99411-e9b3-45b6-9a98-406096d2fa64
-- title:
--   The geometric base change of the same rational order-13 Picard has relative dimension two
-- statement:
--   For every algebraically closed field K of characteristic zero in the exact original universe, the base change of the original actual rational Picard scheme is smooth of relative dimension two over Spec K. The representing scheme is the same original Picard used by the two nineteen norm maps, rather than an independently selected Jacobian. Named downstream consumer: relative dimension two of the original rational Picard and its geometric nineteen-torsion cardinality.
-- source:
--   MazurTheorem, Order13ActualPicardDimensionTwo.lean; Apache-2.0. Complete original theorem type retained, including its original field universe. Uses the accepted field-uniform represented-Picard dimension-two result and the original literal-fibre Picard representation.

import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_MazurTransfer_Order13ActualRationalFunctionFieldTowerOriginalInstancesDataV220261018
noncomputable section
universe u
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra AlgebraicCurve GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
attribute [local instance] Order13ActualRationalFunctionFieldTower.actualRatFuncTowerOriginalFactProvider20261018

open Order13ActualPicardDiamondSchemeEndomorphism

theorem MazurTransfer.Order13ActualPicardDimensionTwo.actualPicard_baseChange_smooth_dimension_two
    (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    SmoothOfRelativeDimension 2 (actualPicard.baseChange K).toBase := by sorry

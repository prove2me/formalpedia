-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardDimensionTwo_actual_represented_picard_smooth_dimension_two
-- name    : MazurTransfer.Order13ActualPicardDimensionTwo.actual_represented_picard_smooth_dimension_two
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T09:16:53.764198+00:00
-- url     : https://prove2.me/theorems/37acdbb9-c19f-4604-95db-841a3284af14
-- title:
--   Every represented Picard of the actual characteristic-zero order-13 curve has relative dimension two
-- statement:
--   For any algebraically closed field K of characteristic zero, any field-rational section ε of the actual order-13 curve, any original RelativePic0Designation D of that same curve and any representation of its algebraically equivalent-to-zero Picard functor at ε, the structural map of D is smooth of relative dimension two. This is the complete original field-uniform statement; the CurveModel and its finite rational-function-field witness are constructed from checked literal-curve data. Named downstream consumer: dimension two of the geometric base change of the original rational Picard, hence its actual nineteen-torsion cardinality.
-- source:
--   MazurTheorem, Order13ActualPicardDimensionTwo.lean and Order13ActualGenusTwoCurveModel.lean, Apache-2.0. Original complete theorem type and original curve-model constructor type and nonproof value checked. The original constructor has no separate PerfectField binder; its exact emitted telescope is preserved. Uses official Anthropic FLT CurveModel dimension-of-genus API at pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

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

theorem MazurTransfer.Order13ActualPicardDimensionTwo.actual_represented_picard_smooth_dimension_two (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroCut (curveToBase K) ε) D) :
    SmoothOfRelativeDimension 2 D.toBase := by sorry

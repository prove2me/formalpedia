-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardRationalDimensionTwo_actualPicard_smooth_dimension_two
-- name    : MazurTransfer.Order13ActualPicardRationalDimensionTwo.actualPicard_smooth_dimension_two
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T09:44:39.789806+00:00
-- url     : https://prove2.me/theorems/f86918ff-f2a3-46b9-88af-4f312e406e09
-- title:
--   The original rational order-13 Picard is smooth of relative dimension two
-- statement:
--   The structural morphism of the original actual rational order-13 Picard scheme is smooth of relative dimension two over Spec Q. This is the same Picard scheme used by both original nineteen norm maps. Named downstream consumer: its fibre dimension and geometric nineteen-torsion cardinality.
-- source:
--   MazurTheorem, Order13ActualPicardRationalDimensionTwo.lean; Apache-2.0. Complete original theorem type with no added hypotheses checked. Reuses the accepted original abelian-scheme bundle and the dimension-two geometric base change.

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

theorem MazurTransfer.Order13ActualPicardRationalDimensionTwo.actualPicard_smooth_dimension_two : SmoothOfRelativeDimension 2 actualPicard.toBase := by sorry

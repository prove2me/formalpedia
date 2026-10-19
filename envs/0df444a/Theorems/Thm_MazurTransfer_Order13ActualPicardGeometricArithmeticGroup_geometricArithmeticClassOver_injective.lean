-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticGroup_geometricArithmeticClassOver_injective
-- name    : MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_injective
-- status  : Open
-- author  : @Vas
-- created : 2026-10-17T20:06:55.65081+00:00
-- url     : https://prove2.me/theorems/8cb6d646-f4c5-41c0-9460-90d35cac6c2f
-- title:
--   The original geometric arithmetic class detects equality of points of the same rational Picard scheme
-- statement:
--   Let K be a perfect characteristic-zero field and choose a two-affine cover of the actual curve over K. For K-valued points a,b of the same original rational represented Picard family, viewed in the over category,
--
--   $$\operatorname{cl}_K(a)=\operatorname{cl}_K(b)\quad\Longrightarrow\quad a=b.$$
--
--   The map is the original arithmetic class from a full degree-zero divisor presentation of the actual geometric line bundle. The result gives the faithful point comparison needed to detect the diamond and nineteen-norm scheme identities.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_injective, retaining all three original unit and kernel helpers and using the accepted exact geometric group law, zero-class criterion and line-bundle point detection. Official Anthropic FLT Poincare identity inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric arithmetic group map on points of the
same existing rational represented Picard is injective. Named downstream
consumer: detection of the actual diamond cyclotomic and scheme norm identities.
Complete original MazurTheorem geometric arithmetic group proof;
official Anthropic FLT Poincare identity inputs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticGroupData
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open MazurTransfer.Order13GeometricRelativeCurveChange
open scoped CategoryTheory.MonObj
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)

theorem MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_injective : Function.Injective (geometricArithmeticClassOver K 𝒱) := by sorry

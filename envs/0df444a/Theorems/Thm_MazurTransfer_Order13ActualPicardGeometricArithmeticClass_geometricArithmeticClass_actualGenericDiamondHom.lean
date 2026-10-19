-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_actualGenericDiamondHom
-- name    : MazurTransfer.Order13ActualPicardGeometricArithmeticClass.geometricArithmeticClass_actualGenericDiamondHom
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:41:03.340291+00:00
-- url     : https://prove2.me/theorems/364f90d3-58cc-49fe-bc6d-08aa7f1e2a93
-- title:
--   The existing rational Picard diamond acts on geometric arithmetic classes by the literal field diamond
-- statement:
--   Let K be a perfect characteristic-zero field and let a be a K-valued point of the same rational represented Picard family. Let δ_Q be the existing generic-compatible rational Picard diamond and let σ_K be the literal diamond automorphism of the actual curve function field over K. Then
--
--   $$\operatorname{cl}_K(\delta_{\mathbf Q}(a))=\sigma_K\cdot\operatorname{cl}_K(a).$$
--
--   The class is computed from the full original geometric degree-zero divisor presentation on the actual curve. This identifies the actual scheme action with the original field automorphism, supplying the geometric input to scheme norm transport.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricArithmeticClass.geometricArithmeticClass_actualGenericDiamondHom, using the public full geometric presentation pullback and accepted presentation independence. Official Anthropic FLT inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same existing rational represented Picard has an
intrinsic degree-zero divisor class at every perfect characteristic-zero
field point. The existing rational diamond transports this class by the
actual extension-field diamond. Named downstream consumer: promoting the
arithmetic diamond cyclotomic relation to a scheme morphism identity.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticClassDataExplicitPublicConstructors20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field

import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle MazurTransfer.Order13ActualPicardGeometricDiamondPresentation
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase)

theorem MazurTransfer.Order13ActualPicardGeometricArithmeticClass.geometricArithmeticClass_actualGenericDiamondHom :
    geometricArithmeticClass K 𝒱
        (postComp (actualFieldHom MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv) a) =
      (MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv K) •
        geometricArithmeticClass K 𝒱 a := by sorry

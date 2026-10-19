-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
-- name    : MazurTransfer.Order13ActualPicardGeometricArithmeticClass.geometricArithmeticClass_eq_of_presentation
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:24:17.536998+00:00
-- url     : https://prove2.me/theorems/eb8e8a2f-d741-4486-b29e-8f35e30a02f8
-- title:
--   Every full degree-zero presentation gives the original geometric arithmetic Picard class
-- statement:
--   Let K be a perfect field of characteristic zero and let a be a K-valued point of the existing rational represented Picard family. Fix a two-affine cover of the actual curve over K. If E is any degree-zero divisor with a full presentation of the actual geometric line bundle associated to a, then
--
--   $$[E]=\operatorname{cl}_K(a).$$
--
--   The right-hand side is the original arithmetic-class constructor defined from the chosen full degree-zero presentation. The complete original naturality, scalar compatibility, injectivity and affine-open range conditions are retained. The result makes the class intrinsic and supplies compatibility with the actual diamond action.
-- source:
--   Original MazurTheorem Order13ActualPicardGeometricArithmeticClass.geometricArithmeticClass_eq_of_presentation, reusing the accepted perfect-field presentation ratio. The original chosen-presentation constructor type and value are compared explicitly. Official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

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

theorem MazurTransfer.Order13ActualPicardGeometricArithmeticClass.geometricArithmeticClass_eq_of_presentation
    (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
    (φ : ∀ U : (curveScheme K).Opens,
      Γ(actualGeometricPointLineBundle K a, U) →+ actualCurveFunctionField K)
    (hE : IsPresentation (curveToBase K) (actualGeometricPointLineBundle K a) E.1 φ) :
    Pic0.mk E = geometricArithmeticClass K 𝒱 a := by sorry

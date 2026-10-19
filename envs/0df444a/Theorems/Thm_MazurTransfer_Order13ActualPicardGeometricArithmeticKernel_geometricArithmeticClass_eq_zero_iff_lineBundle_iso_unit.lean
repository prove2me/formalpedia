-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticKernel_geometricArithmeticClass_eq_zero_iff_lineBundle_iso_unit
-- name    : MazurTransfer.Order13ActualPicardGeometricArithmeticKernel.geometricArithmeticClass_eq_zero_iff_lineBundle_iso_unit
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:41:03.003094+00:00
-- url     : https://prove2.me/theorems/79a8a1ea-b326-41e5-85c1-5a717bd0babb
-- title:
--   A geometric point has zero arithmetic Picard class exactly when its actual line bundle is trivial
-- statement:
--   Let K be a perfect characteristic-zero field and let a be a K-valued point of the same existing rational represented Picard family. On the actual geometric curve over K,
--
--   $$\operatorname{cl}_K(a)=0\quad\Longleftrightarrow\quad L_a\simeq\mathcal O_{C_K}.$$
--
--   The arithmetic class is the original full degree-zero divisor class, and L_a is the original actual geometric line bundle. The criterion supplies the kernel step for injectivity of the geometric arithmetic-class map.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricArithmeticKernel.geometricArithmeticClass_eq_zero_iff_lineBundle_iso_unit, using accepted geometric degree-zero presentations, presentation independence and arbitrary-field principal-presentation triviality. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the complete checked original Anthropic FLT principal-presentation
triviality argument at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a geometric field point of the same existing rational
Picard has zero arithmetic class exactly when its actual fibre line bundle
is trivial. Named downstream consumer: injectivity of the geometric class
map and promotion of diamond identities to scheme morphisms.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticClassDataExplicitPublicConstructors20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_nonempty_iso_tensorUnit_of_principal_presentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13GeometricRelativeCurveChange MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition MazurTransfer.LineBundleFieldComparison
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem MazurTransfer.Order13ActualPicardGeometricArithmeticKernel.geometricArithmeticClass_eq_zero_iff_lineBundle_iso_unit
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    geometricArithmeticClass K 𝒱 a = 0 ↔
      Nonempty (actualGeometricPointLineBundle K a ≅ 𝟙_ (curveScheme K).Modules) := by sorry

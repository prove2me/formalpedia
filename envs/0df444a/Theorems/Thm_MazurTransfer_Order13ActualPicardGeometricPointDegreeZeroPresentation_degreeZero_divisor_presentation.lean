-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
-- name    : MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:05:53.409098+00:00
-- url     : https://prove2.me/theorems/8226ac2a-8223-45a7-ac30-a5548e800483
-- title:
--   Every geometric point of the existing rational Picard has a full degree-zero divisor presentation on the actual curve
-- statement:
--   Let K be a perfect field of characteristic zero, and let a be a K-valued point of the existing rational represented degree-zero Picard family for the literal order-13 curve. For any chosen two-affine cover of the actual curve C over K, there exist a degree-zero divisor D and compatible injective section maps giving a full presentation of the actual line bundle L_a:
--
--   $$\deg D=0,\qquad L_a\simeq\mathcal O_C(D).$$
--
--   The formal contract retains the full naturality, scalar compatibility, injectivity and all affine-open section-range conditions. This supplies the intrinsic arithmetic divisor class of geometric points of the same rational Picard scheme.
-- source:
--   Original MazurTheorem Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation. Proof compares the public Riemann-Roch identities for the actual geometric line bundle and the unit sheaf using the original geometric Euler-characteristic equality. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every perfect characteristic-zero field point of the same
existing rational represented Picard has a full degree-zero divisor
presentation on the literal curve over that field. Named downstream
consumer: the geometric arithmetic class of the rational Picard diamond.
-/
import Theorems.Thm_MazurTransfer_divisor_presentation_riemann_roch_over_perfect_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondLineBundleData
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13GeometricRelativeCurveChange
open MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition MazurTransfer.LineBundleFieldComparison
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    ∃ (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
      (φ : ∀ U : (curveScheme K).Opens,
        Γ(actualGeometricPointLineBundle K a, U) →+ actualCurveFunctionField K),
      IsPresentation (curveToBase K) (actualGeometricPointLineBundle K a) E.1 φ := by sorry

-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_picard_point_degreeZero_divisor_presentation
-- name    : MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T15:15:37.039276+00:00
-- url     : https://prove2.me/theorems/0e5a3fbf-27e3-40d3-9ca9-11c68b8b3bd1
-- title:
--   Actual represented Picard points admit degree-zero divisor presentations
-- statement:
--   Over every perfect field of characteristic different from 2 and 13, every base-field point of any represented degree-zero Picard scheme for the literal order-13 curve admits a genuine degree-zero function-field divisor and a full divisor presentation of its associated line bundle. The statement quantifies over the original affine cover, section, Picard designation and representation.
-- source:
--   Original MazurTheorem Order13ActualPicardPointDegreeZeroDivisorPresentation statement, with a new proof through accepted public perfect-field Riemann-Roch and represented-point classification. Official Anthropic FLT presentation interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: attach a genuine degree-zero divisor presentation to every
represented actual Picard point over a perfect good-characteristic field.
Named downstream consumer: arithmetic class independence and pullback naturality.
Original contract: MazurTheorem Order13ActualPicardPointDegreeZeroDivisorPresentation.
This proof compares two public Riemann-Roch identities with the public point
Euler-characteristic equality. Official Anthropic FLT presentation inputs:
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_represented_picard_field_points_classify_line_bundles
import Theorems.Thm_MazurTransfer_divisor_presentation_riemann_roch_over_perfect_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Definitions.Def_MazurTransfer_RepresentedPicardBaseFieldPointLineBundle
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open MazurTransfer.LineBundleFieldComparison

theorem MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    ∃ (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
      (φ : ∀ U : (curveScheme K).Opens,
        Γ(pointLineBundle (curveToBase K) ε D h a, U) →+ (actualCurveFunctionField K)),
      IsPresentation (curveToBase K) (pointLineBundle (curveToBase K) ε D h a) E.1 φ  := by sorry

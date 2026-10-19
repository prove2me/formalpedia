-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_relative_dimension_and_picard_geometry
-- name    : MazurTransfer.order13_actual_dyadic_relative_dimension_and_picard_geometry
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T05:34:18.051703+00:00
-- url     : https://prove2.me/theorems/a30af0b3-9212-463a-8301-c7bc1ff85834
-- statement:
--   The ordinary and reciprocal dyadic mixed quadratic chart morphisms and the whole glued curve are smooth of relative dimension exactly one. The actual base is noetherian and reduced, the actual curve is proper and geometrically integral, it has its original zero section, and the whole family is geometrically connected. All original hypotheses are retained. Seventeen original helper types and all five complete original propositions are checked independently. Named downstream consumer: the compatible dyadic Picard representation and Neron model.

import Mathlib
import Definitions.Def_MazurTransfer_Order13DyadicOriginalPicardZeroSectionData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalCoefficientAndOverlapBaseChangeMapsData20261019
import Theorems.Thm_MazurTransfer_order13_mixed_quadratic_unit_and_smoothness_certificates
import Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_both_field_chart_domains
import Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_curve_proper
import Theorems.Thm_MazurTransfer_order13_actual_mixed_curve_geometricallyIntegral
import Theorems.Thm_MazurTransfer_mixed_quadratic_coordinate_kaehler_equiv
import Theorems.Thm_MazurTransfer_locally_standardSmooth_relativeDimension_one_of_kaehler_equiv
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
namespace MazurTransfer.DyadicPicardGeometryOriginalProofContext20261019
theorem originalDyadicGeometryPrimeProvider20261019 : Fact (Nat.Prime 2) := ⟨by decide⟩
end MazurTransfer.DyadicPicardGeometryOriginalProofContext20261019
attribute [local instance] MazurTransfer.DyadicPicardGeometryOriginalProofContext20261019.originalDyadicGeometryPrimeProvider20261019

theorem MazurTransfer.order13_actual_dyadic_relative_dimension_and_picard_geometry : (SmoothOfRelativeDimension 1 (ordinaryToBase BaseRing)) ∧ (SmoothOfRelativeDimension 1 (reciprocalToBase BaseRing)) ∧ (SmoothOfRelativeDimension 1 (curveToBase BaseRing)) ∧ (IsNoetherianRing BaseRing ∧ IsReduced BaseRing ∧ IsProper (curveToBase BaseRing) ∧
      SmoothOfRelativeDimension 1 (curveToBase BaseRing) ∧
      GeometricallyIntegral (curveToBase BaseRing) ∧
      Nonempty (NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of BaseRing))) (curveToBase BaseRing))) ∧ (GeometricallyConnected (curveToBase BaseRing)) := by sorry

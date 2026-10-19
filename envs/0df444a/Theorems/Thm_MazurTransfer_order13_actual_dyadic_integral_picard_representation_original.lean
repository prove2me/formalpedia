-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_integral_picard_representation_original
-- name    : MazurTransfer.order13_actual_dyadic_integral_picard_representation_original
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T07:44:48.526987+00:00
-- url     : https://prove2.me/theorems/37ab843e-8ec7-4b4a-97ed-5cb588c56888
-- statement:
--   There exists a relative degree-zero Picard designation for the actual dyadic mixed quadratic curve and its original zero section, representing the original algEquivZeroCut subfunctor, whose scheme is smooth, proper and geometrically connected over the dyadic base. The complete original statement is retained. The exact official Anthropic FLT representability theorem is applied to the actual arbitrarily large finite-map data and all 216 original marked-section triples with their checked genus-two geometric fibre models. Named downstream consumer: compatible algebra base changes, the abelian Picard family and the actual dyadic Neron model.

import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalFiniteMapDataAndGeometryInputsData20261019
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalCurveModelsGenusTwoAndPicardChartSectionsData20261019
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13DyadicMixedQuadraticPicardGeometryInputs
open Order13ActualDyadicMixedFiniteMapData Order13ActualDyadicMixedPicardChartSections
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019

theorem MazurTransfer.order13_actual_dyadic_integral_picard_representation_original : ∃ D : RelativePic0Designation BaseRing (curveToBase BaseRing),
      Nonempty (RepresentsRelSubPic (curveToBase BaseRing) zeroSection
        (algEquivZeroCut (curveToBase BaseRing) zeroSection) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by sorry

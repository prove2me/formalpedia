-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_mixed_affine_chart_geometry
-- name    : MazurTransfer.order13_actual_dyadic_mixed_affine_chart_geometry
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T02:27:56.775356+00:00
-- url     : https://prove2.me/theorems/b6707ccb-6305-4fdc-b697-c35e4f3fead2
-- statement:
--   Both actual ordinary and reciprocal mixed quadratic affine chart morphisms over the integers localized at two are smooth, flat and locally of finite presentation. The result retains the original literal coordinate algebras and structural morphisms. It uses the original odd integral Jacobian constants and imposes no invertibility-of-two condition. The named downstream consumer is proper gluing and the same dyadic Picard model.

import Definitions.Def_MazurTransfer_Order13DyadicMixedOriginalAffineChartData20261019
import Theorems.Thm_MazurTransfer_order13_mixed_quadratic_unit_and_smoothness_certificates
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13DyadicMixedQuadraticCharts
attribute [local instance] dyadicChartOriginalPrimeTwoProvider20261019

theorem MazurTransfer.order13_actual_dyadic_mixed_affine_chart_geometry :
    (Smooth (ordinaryToBase BaseRing) ∧ Flat (ordinaryToBase BaseRing) ∧
      LocallyOfFinitePresentation (ordinaryToBase BaseRing)) ∧
    (Smooth (reciprocalToBase BaseRing) ∧ Flat (reciprocalToBase BaseRing) ∧
      LocallyOfFinitePresentation (reciprocalToBase BaseRing)) := by sorry

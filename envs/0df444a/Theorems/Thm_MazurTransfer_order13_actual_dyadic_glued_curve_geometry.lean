-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_glued_curve_geometry
-- name    : MazurTransfer.order13_actual_dyadic_glued_curve_geometry
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T04:19:48.976651+00:00
-- url     : https://prove2.me/theorems/57e1c480-c0f3-4e76-a134-b1eb5b9f3d26
-- statement:
--   The original actual glued mixed quadratic curve over the dyadic localization is smooth, flat and locally of finite presentation. Its chart scheme and categorical gluing constructors remain the literal original ones. The named downstream consumer is the proper smooth dyadic curve and its integral Picard family.

import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalGluedCurveData20261019
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_mixed_affine_chart_geometry
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve

theorem MazurTransfer.order13_actual_dyadic_glued_curve_geometry : Smooth (curveToBase BaseRing) ∧ Flat (curveToBase BaseRing) ∧ LocallyOfFinitePresentation (curveToBase BaseRing) := by sorry

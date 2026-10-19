-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_finite_map_data_and_geometry_certificates
-- name    : MazurTransfer.order13_actual_dyadic_finite_map_data_and_geometry_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T07:20:44.435986+00:00
-- url     : https://prove2.me/theorems/c7092d50-9a3e-4a3f-a2d7-8911d8fd0031
-- statement:
--   For the original dyadic mixed quadratic curve with its chosen original zero section, the explicit degree-three finite-map datum and every positive power have their original exact degrees. Finite-map data exist above every prescribed degree bound. The same curve is proper, smooth of relative dimension one and geometrically integral over the original reduced Noetherian dyadic ring. All four complete original propositions, including every quantifier, are retained. Named downstream consumer: representability of the actual relative degree-zero Picard functor.

import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalFiniteMapDataAndGeometryInputsData20261019
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13DyadicMixedQuadraticPicardGeometryInputs Order13ActualDyadicMixedFiniteMapData
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedFiniteMapData.originalDyadicFiniteMapPrimeProvider20261019

theorem MazurTransfer.order13_actual_dyadic_finite_map_data_and_geometry_certificates : (dyadicFiniteMapData.m = 3) ∧ (∀ (n : ℕ) (hn : n ≠ 0), (dyadicPowerFiniteMapData n hn).m = n * 3) ∧ (∀ (m₀ : ℕ), ∃ F : SmoothProperCurve.FiniteMapData (curveToBase BaseRing) zeroSection, m₀ ≤ F.m) ∧ (IsNoetherianRing BaseRing ∧ IsReduced BaseRing ∧ IsProper (curveToBase BaseRing) ∧
    SmoothOfRelativeDimension 1 (curveToBase BaseRing) ∧
    GeometricallyIntegral (curveToBase BaseRing) ∧
    (∀ m₀, ∃ F : SmoothProperCurve.FiniteMapData (curveToBase BaseRing) zeroSection, m₀ ≤ F.m)) := by sorry

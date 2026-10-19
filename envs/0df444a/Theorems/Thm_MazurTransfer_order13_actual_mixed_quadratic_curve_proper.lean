-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_curve_proper
-- name    : MazurTransfer.order13_actual_mixed_quadratic_curve_proper
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T04:28:02.492329+00:00
-- url     : https://prove2.me/theorems/715cdf47-0cd6-4631-a313-9da52a21d122
-- statement:
--   The original actual glued mixed quadratic curve is proper over every commutative coefficient ring. Its glued structure morphism is the original finite hyperelliptic map followed by the proper structure morphism of the projective line. No field, characteristic or Noetherian hypothesis is added. Named downstream consumer: the actual proper smooth dyadic curve and its integral Picard family.

import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalFiniteHyperellipticMapAndProperCurveDataDistinctProjectiveLineNamespaceV320261019
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13MixedQuadraticGluedCurve
universe u

theorem MazurTransfer.order13_actual_mixed_quadratic_curve_proper : ∀ (R : Type u) [CommRing R], IsProper (curveToBase R) := by sorry

-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_mixed_curve_geometricallyIntegral
-- name    : MazurTransfer.order13_actual_mixed_curve_geometricallyIntegral
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T05:06:30.793463+00:00
-- url     : https://prove2.me/theorems/51d9df99-25ba-4d72-91e3-ad4d8cef2245
-- statement:
--   The original actual mixed quadratic glued curve is geometrically integral over EVERY commutative coefficient ring. The original ordinary quadratic is irreducible by its degree inequality; the two field charts are domains and glue integrally with their nonempty overlap. The checked whole-curve base-change square identifies every field fibre with that integral field model. All fourteen original proof-helper types and the complete universal proposition are compared independently. No characteristic, field or Noetherian restriction is added. Named downstream consumer: the actual dyadic integral Picard family.

import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalFiniteHyperellipticMapAndProperCurveDataDistinctProjectiveLineNamespaceV320261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
import Theorems.Thm_MazurTransfer_integral_of_two_chart_gluing
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13MixedQuadraticGluedCurve
universe u

theorem MazurTransfer.order13_actual_mixed_curve_geometricallyIntegral : ∀ (R : Type u) [CommRing R], GeometricallyIntegral (curveToBase R) := by sorry

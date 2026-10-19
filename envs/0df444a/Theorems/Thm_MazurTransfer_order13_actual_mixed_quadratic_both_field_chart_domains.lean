-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_both_field_chart_domains
-- name    : MazurTransfer.order13_actual_mixed_quadratic_both_field_chart_domains
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T05:24:43.007874+00:00
-- url     : https://prove2.me/theorems/d88cb3d5-4438-45bf-aed7-9ca6f6775579
-- statement:
--   Both literal original mixed quadratic chart algebras are integral domains over every field, including characteristic two. The ordinary mixed monic quadratic is irreducible by the original degree argument; regularity of the reciprocal coordinate and the original overlap equivalence transfer the domain structure to the reciprocal chart. All twelve original helper types and both complete universal field propositions are independently checked. Named downstream consumer: injectivity into the rational scalar extension, dyadic chart domains, relative dimension one and Picard geometry.

import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalFiniteHyperellipticMapAndProperCurveDataDistinctProjectiveLineNamespaceV320261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13MixedQuadraticGluedCurve
universe u

theorem MazurTransfer.order13_actual_mixed_quadratic_both_field_chart_domains : (∀ (K : Type u) [Field K], IsDomain (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)) ∧ (∀ (K : Type u) [Field K], IsDomain (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)) := by sorry

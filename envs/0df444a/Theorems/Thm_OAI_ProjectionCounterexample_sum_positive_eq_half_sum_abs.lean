-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_sum_positive_eq_half_sum_abs
-- name    : OAI.ProjectionCounterexample.sum_positive_eq_half_sum_abs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:59:29.149344+00:00
-- url     : https://prove2.me/theorems/842df1c6-1695-487d-a063-7fcff31702f2
-- title:
--   In a zero-sum family, the positive terms add up to half the total absolute value
-- statement:
--   Let $\iota$ be a finite index set and $(a_i)_{i\in\iota}$ a family of real numbers whose total sum is zero, $\sum_{i\in\iota}a_i=0$.
--
--   **Theorem.**
--   $$
--   \sum_{i\in\iota:\ a_i>0}a_i=\frac12\sum_{i\in\iota}|a_i| .
--   $$
--
--   When the positive and the negative terms of a balanced family cancel, each group carries half of the total absolute mass. In the computation of projection volumes of polytopes, the $a_i$ are the values at the projection direction of the facet functionals, and the identity turns the sum over the visible facets (those with $a_i>0$) into a symmetric expression in all $|a_i|$.
--
--   **Formalization Note** The left-hand side is the filtered sum `∑ i with 0 < a i, a i` over all elements of a `Fintype`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/Arithmetic.lean#L13-L30

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Definitions.Def_ProjectionCounterexample
import Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
import Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCoordinates
import Definitions.Def_OAI_Geometry_ProjectionBody_GraphChart
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacetCharts
import Definitions.Def_OAI_Geometry_Zonotope_Decomposition
import Definitions.Def_OAI_Geometry_Zonotope_Support
import Definitions.Def_OAI_Geometry_Zonotope_Euclidean
import Definitions.Def_OAI_Geometry_Zonotope_Product
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetCharts
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetGraphs
import Definitions.Def_OAI_Geometry_ProjectionBody_HyperplaneJacobian
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexVolume

open OAI OAI.ProjectionCounterexample

theorem OAI.ProjectionCounterexample.sum_positive_eq_half_sum_abs {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    (∑ i with 0 < a i, a i) = (∑ i, |a i|) / 2 := by sorry

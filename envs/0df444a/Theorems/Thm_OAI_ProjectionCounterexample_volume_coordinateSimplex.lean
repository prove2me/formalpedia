-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_volume_coordinateSimplex
-- name    : OAI.ProjectionCounterexample.volume_coordinateSimplex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:57:49.098003+00:00
-- url     : https://prove2.me/theorems/9085c43a-1356-417f-b4e9-e21215fb2bd7
-- title:
--   The simplex $\{x\ge 0,\ \sum_i x_i\le r\}$ in $\mathbb{R}^n$ has volume $r^n/n!$
-- statement:
--   For $n\in\mathbb{N}$ and $r\in\mathbb{R}$ let
--   $$
--   \Delta_n(r)=\Big\{x\in\mathbb{R}^n:\ x_i\ge0\ \text{for all } i,\ \ \sum_{i}x_i\le r\Big\}
--   $$
--   be the standard simplex of size $r$, and let $\lambda_n$ be Lebesgue measure on $\mathbb{R}^n$.
--
--   **Theorem.** If $r\ge0$, then
--   $$
--   \lambda_n\big(\Delta_n(r)\big)=\frac{r^n}{n!}.
--   $$
--
--   The case $r=1$ is the classical volume $1/n!$ of the standard simplex. In the projection-body computations it supplies the volume of the simplex, the volumes of the parameter domains of its facets (which are lower-dimensional standard simplices), and, through the product formula, the volume of a product of two simplices.
--
--   **Formalization Note** The simplex lives in the function space `Fin n → ℝ` with its product Lebesgue measure `volume`, which takes values in $[0,\infty]$; the right-hand side is `ENNReal.ofReal` applied to the real number $r^n/n!$. For $n=0$ the space is a single point, the conditions reduce to $0\le r$, and both sides equal $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/SimplexVolume.lean#L63-L110

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
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem OAI.ProjectionCounterexample.volume_coordinateSimplex (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (coordinateSimplex n r) =
      ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by sorry

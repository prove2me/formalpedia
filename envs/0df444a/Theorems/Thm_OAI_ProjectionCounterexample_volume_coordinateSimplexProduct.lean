-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_volume_coordinateSimplexProduct
-- name    : OAI.ProjectionCounterexample.volume_coordinateSimplexProduct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:58:41.384493+00:00
-- url     : https://prove2.me/theorems/aef8dc95-6457-4898-b6c7-2f978d7c1393
-- title:
--   A product of two standard simplices has volume $1/(p!\,q!)$
-- statement:
--   For $k\in\mathbb{N}$ let $\Delta_k=\{y\in\mathbb{R}^k:\ y_i\ge0\ \text{for all }i,\ \sum_i y_i\le1\}$ be the standard simplex. For $p,q\in\mathbb{N}$ consider the product of two such simplices placed in the first $p$ and the last $q$ coordinates of $\mathbb{R}^{p+q}$,
--   $$
--   \Delta_p\times\Delta_q=\big\{x\in\mathbb{R}^{p+q}:\ (x_0,\dots,x_{p-1})\in\Delta_p,\ \ (x_p,\dots,x_{p+q-1})\in\Delta_q\big\},
--   $$
--   and let $\lambda_{p+q}$ be Lebesgue measure on $\mathbb{R}^{p+q}$.
--
--   **Theorem.** For all $p,q\in\mathbb{N}$,
--   $$
--   \lambda_{p+q}(\Delta_p\times\Delta_q)=\frac{1}{p!\,q!}.
--   $$
--
--   In the projection-body computation, the case $p=q=10$ gives the volume $1/(10!)^2$ of the product body $T_{10}\times T_{10}\subset\mathbb{R}^{20}$, and the cases $(p,q)=(9,10)$ and $(10,9)$ give the volumes of the parameter domains of its facet charts.
--
--   **Formalization Note** The set is `coordinateSimplexProduct p q`, a subset of `Fin (p + q) → ℝ` whose first and last blocks are read off with `Fin.castAdd` and `Fin.natAdd`. The measure is the product Lebesgue measure `volume` with values in $[0,\infty]$, and the right-hand side is `ENNReal.ofReal` applied to the real number $1/(p!\,q!)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/SimplexVolume.lean#L150-L172

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

theorem OAI.ProjectionCounterexample.volume_coordinateSimplexProduct (p q : ℕ) :
    volume (coordinateSimplexProduct p q) =
      ENNReal.ofReal (1 / ((p.factorial : ℝ) * (q.factorial : ℝ))) := by sorry

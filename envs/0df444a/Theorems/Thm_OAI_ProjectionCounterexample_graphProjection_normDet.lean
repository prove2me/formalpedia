-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_graphProjection_normDet
-- name    : OAI.ProjectionCounterexample.graphProjection_normDet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:56:04.919551+00:00
-- url     : https://prove2.me/theorems/9679f476-cbaa-47d7-8466-7dfdc26ce08a
-- title:
--   The projected area factor of a graph chart is $|\langle N,u\rangle|$ for its unnormalized normal $N$
-- statement:
--   Index the coordinates of $\mathbb{R}^{d}$ by $\{0,\dots,d-1\}$, let $e_k$ be the standard basis vectors, and for $0\le k\le n$ let $\iota_k:\mathbb{R}^n\to\mathbb{R}^{n+1}$ insert a zero in slot $k$. For $a\in\mathbb{R}^n$ let
--   $$
--   G_{k,a}(x)=\iota_k(x)-\langle a,x\rangle\, e_k,\qquad N_{k,a}=\iota_k(a)+e_k
--   $$
--   be the graph chart $\mathbb{R}^n\to\mathbb{R}^{n+1}$ (it writes $x$ in the slots other than $k$ and $-\langle a,x\rangle$ in slot $k$) and its unnormalized normal. For a unit vector $u\in\mathbb{R}^{n+1}$ let $P_u$ be the orthogonal projection of $\mathbb{R}^{n+1}$ onto $u^\perp$. For a linear map $A$ on $\mathbb{R}^n$ let $J(A)=\sqrt{\det(A^{*}A)}$ be its norm determinant, the factor by which $A$ scales $n$-dimensional volume.
--
--   **Theorem.** For every $n\ge0$, $k\in\{0,\dots,n\}$, $a\in\mathbb{R}^n$ and every unit vector $u\in\mathbb{R}^{n+1}$,
--   $$
--   J(P_u\circ G_{k,a})=|\langle N_{k,a},u\rangle| .
--   $$
--   In particular, for $a=0$ the chart is the coordinate insertion $\iota_k$ with normal $e_k$, and the factor is $|u_k|$.
--
--   The length of the unnormalized normal cancels: the chart stretches $n$-dimensional volume by $\|N_{k,a}\|$, and the projection shrinks it by the cosine $|\langle N_{k,a},u\rangle|/\|N_{k,a}\|$. This expresses the projected area factor of every facet chart of a simplex, or of a product of simplices, as the absolute value of the facet's outward functional evaluated at $u$.
--
--   **Formalization Note** $P_u$ is `project u`, the orthogonal projection onto the orthogonal complement of the span of $u$, which is the projection used in the definition of projection volumes. The chart is `graphLinear k a`, the normal is `graphNormal k a`, and $J$ is Mathlib's `LinearMap.normDet`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/GraphProjection.lean#L13-L31

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

open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace

theorem OAI.ProjectionCounterexample.graphProjection_normDet {n : ℕ} (i : Fin (n + 1)) (a : E n)
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (graphLinear i a)).normDet =
      |⟪graphNormal i a, u⟫| := by sorry

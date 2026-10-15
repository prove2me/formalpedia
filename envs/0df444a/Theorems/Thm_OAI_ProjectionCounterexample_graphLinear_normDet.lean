-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_graphLinear_normDet
-- name    : OAI.ProjectionCounterexample.graphLinear_normDet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:52:43.082904+00:00
-- url     : https://prove2.me/theorems/57e66cc8-e621-49cc-a967-e2841d324b3b
-- title:
--   The norm determinant of a linear graph chart is the length of its normal
-- statement:
--   Index the coordinates of $\mathbb{R}^d$ by $\{0,\dots,d-1\}$ and let $e_k$ be the standard basis vectors. Fix $n\ge0$, a slot $k\in\{0,\dots,n\}$ and a vector $a\in\mathbb{R}^n$. Let $\iota_k:\mathbb{R}^n\to\mathbb{R}^{n+1}$ insert a zero in slot $k$, and define the graph chart and its unnormalized normal
--   $$
--   G_{k,a}(x)=\iota_k(x)-\langle a,x\rangle\,e_k,\qquad N_{k,a}=\iota_k(a)+e_k\in\mathbb{R}^{n+1}.
--   $$
--   Thus $G_{k,a}$ writes $x$ in the slots other than $k$ and $-\langle a,x\rangle$ in slot $k$, while $N_{k,a}$ has entry $1$ in slot $k$ and the entries of $a$ elsewhere; $N_{k,a}$ is orthogonal to the image of $G_{k,a}$. For a linear map $L$ out of a finite-dimensional real inner product space $U$, let $J(L)=\sqrt{\det(L^{*}L)}$ be its norm determinant, the factor by which $L$ scales $(\dim U)$-dimensional volume (it vanishes when $L$ is not injective).
--
--   **Theorem.** The norm determinant of a graph chart is the length of its unnormalized normal:
--   $$
--   J(G_{k,a})=\|N_{k,a}\| .
--   $$
--   Since $\|N_{k,a}\|^2=1+\|a\|^2$, the common value is $\sqrt{1+\|a\|^2}$.
--
--   This is the linear case of the classical area element $\sqrt{1+|\nabla f|^2}$ of a graph: combined with the area formula for linear maps, it says that the $n$-dimensional measure of $G_{k,a}(A)$ is $\|N_{k,a}\|$ times the volume of $A\subseteq\mathbb{R}^n$. It is combined with the hyperplane projection formula to compute the projected areas of polytope facets that are parametrized as graphs.
--
--   **Formalization Note** $J$ is Mathlib's `LinearMap.normDet`: the absolute value of the determinant of the map onto its range in orthonormal bases when the dimensions match, and $0$ otherwise; its square is the Gram determinant of the images of an orthonormal basis. The chart and normal are `graphLinear k a` and `graphNormal k a` with `k : Fin (n + 1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/GraphJacobian.lean#L12-L34

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

open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace

theorem OAI.ProjectionCounterexample.graphLinear_normDet {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    (graphLinear i a).normDet = ‖graphNormal i a‖ := by sorry

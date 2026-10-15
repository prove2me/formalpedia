-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_productFacetLinear_first_sum
-- name    : OAI.ProjectionCounterexample.productFacetLinear_first_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:50:52.873429+00:00
-- url     : https://prove2.me/theorems/1a3a7e16-7de8-4e00-8d92-fb1ef5c11501
-- title:
--   The first-block sum facet chart of $T_{10}\times T_{10}$ is a graph chart
-- statement:
--   Index the coordinates of $\mathbb{R}^d$ by $\{0,1,\dots,d-1\}$ and let $e_k$ be the standard basis vectors. For $0\le k\le n$ let $\iota_k:\mathbb{R}^n\to\mathbb{R}^{n+1}$ insert a zero in slot $k$, and for $a\in\mathbb{R}^n$ let the *graph chart* $G_{k,a}:\mathbb{R}^n\to\mathbb{R}^{n+1}$ be
--   $$
--   G_{k,a}(x)=\iota_k(x)-\langle a,x\rangle\,e_k ,
--   $$
--   which writes $x$ in the slots other than $k$ (in increasing order) and $-\langle a,x\rangle$ in slot $k$. Its image is the hyperplane orthogonal to $\iota_k(a)+e_k$.
--
--   Let $T_{10}\subset\mathbb{R}^{10}$ be the standard simplex and view $T_{10}\times T_{10}$ inside $\mathbb{R}^{20}$, the first factor occupying $x_0,\dots,x_9$ and the second $x_{10},\dots,x_{19}$. The facet $\{x_0+\dots+x_9=1\}$ of the product (the sum facet of the first factor) is parametrized by an affine chart on $\mathbb{R}^{19}$ whose linear part is
--   $$
--   \Lambda_{1,*}(x)=\big(\gamma(z),\ w\big),\qquad z=(x_0,\dots,x_8)\in\mathbb{R}^{9},\quad w=(x_9,\dots,x_{18})\in\mathbb{R}^{10},
--   $$
--   where $\gamma=G_{9,\mathbf 1_9}:\mathbb{R}^9\to\mathbb{R}^{10}$, $\gamma(z)=(z_0,\dots,z_8,-(z_0+\dots+z_8))$, is the linear part of the chart of the sum facet of $T_{10}$, and $\mathbf 1_9$ is the all-ones vector.
--
--   **Theorem.** The chart map $\Lambda_{1,*}$ is itself a graph chart of $\mathbb{R}^{20}$ with slot $9$:
--   $$
--   \Lambda_{1,*}=G_{9,a},\qquad a=(\underbrace{1,\dots,1}_{9},\underbrace{0,\dots,0}_{10})\in\mathbb{R}^{19},
--   $$
--   that is, $\Lambda_{1,*}(x)=(x_0,\dots,x_8,\,-(x_0+\dots+x_8),\,x_9,\dots,x_{18})$ for all $x\in\mathbb{R}^{19}$.
--
--   The identity puts the chart of this facet into the normal form of a graph chart, whose unnormalized normal $\iota_9(a)+e_9=(1,\dots,1,0,\dots,0)$ (ten ones followed by ten zeros) is the outward normal direction of the facet. The general formula for projected area factors of graph charts then gives the value $|u_0+\dots+u_9|$ for this facet.
--
--   **Formalization Note** The facet index is `(false, none)` in `Bool × Option (Fin 10)`. The vector $a$ is `firstSumGraph`, the concatenation of `allOnes 9` and $0\in\mathbb{R}^{10}$ via `EuclideanSpace.finAddEquivProd`, and the slot is `(Fin.last 9).castAdd 10`, i.e. $9$. `graphLinear k a` is $G_{k,a}$ and `insertZero k` is $\iota_k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductFacetGraphs.lean#L103-L124

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

theorem OAI.ProjectionCounterexample.productFacetLinear_first_sum :
    productFacetLinear (false, none) = graphLinear ((Fin.last 9).castAdd 10) firstSumGraph := by sorry

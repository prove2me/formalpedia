-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_productFacetLinear_second_coordinate
-- name    : OAI.ProjectionCounterexample.productFacetLinear_second_coordinate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:50:32.888628+00:00
-- url     : https://prove2.me/theorems/c0172a2f-c426-441e-b159-5d5aa8a7e3a0
-- title:
--   Second-block coordinate facet charts of $T_{10}\times T_{10}$ are coordinate insertions
-- statement:
--   Index the coordinates of $\mathbb{R}^d$ by $\{0,1,\dots,d-1\}$. For $0\le k\le n$ let $\iota_k:\mathbb{R}^n\to\mathbb{R}^{n+1}$ be the linear isometry that inserts a zero in slot $k$, $\iota_k(x_0,\dots,x_{n-1})=(x_0,\dots,x_{k-1},0,x_k,\dots,x_{n-1})$.
--
--   Let $T_{10}\subset\mathbb{R}^{10}$ be the standard simplex and view the product $T_{10}\times T_{10}$ inside $\mathbb{R}^{20}$, the first factor occupying the coordinates $x_0,\dots,x_9$ and the second factor the coordinates $x_{10},\dots,x_{19}$. For $i\in\{0,\dots,9\}$, the facet $\{x_{10+i}=0\}$ of the product (the coordinate facet $\{y_i=0\}$ of the second factor) is parametrized by an affine chart on $\mathbb{R}^{19}$ whose linear part is
--   $$
--   \Lambda_{2,i}(x)=\big(z,\ \iota_i(w)\big),\qquad z=(x_0,\dots,x_9)\in\mathbb{R}^{10},\quad w=(x_{10},\dots,x_{18})\in\mathbb{R}^{9},
--   $$
--   that is, the first ten coordinates of $x\in\mathbb{R}^{19}$ are kept as the first block, and the zero insertion $\iota_i$ is applied to the last nine coordinates to form the second block.
--
--   **Theorem.** For every $i\in\{0,\dots,9\}$ the map $\Lambda_{2,i}$ is the single coordinate insertion at slot $10+i$, i.e. $\Lambda_{2,i}=\iota_{10+i}$ as linear maps $\mathbb{R}^{19}\to\mathbb{R}^{20}$:
--   $$
--   \Lambda_{2,i}(x)=(x_0,\dots,x_{9+i},\,0,\,x_{10+i},\dots,x_{18})\qquad\text{for all }x\in\mathbb{R}^{19}.
--   $$
--
--   The identity rewrites the block-wise chart of a second-factor coordinate facet as a plain coordinate chart of $\mathbb{R}^{20}$, so that general results about coordinate and graph charts apply to it directly; for instance, after orthogonal projection onto $u^\perp$ its area factor is $|u_{10+i}|$. Together with its first-block analogue and the two sum-facet identities, it identifies all $22$ facet charts of $T_{10}\times T_{10}$ with coordinate insertions or graph charts.
--
--   **Formalization Note** Facets of the product are indexed by `Bool × Option (Fin 10)`; the index `(true, some i)` is coordinate facet $i$ of the second block. `productFacetLinear (true, some i)` is defined by splitting $\mathbb{R}^{19}\cong\mathbb{R}^{10}\times\mathbb{R}^{9}$ and $\mathbb{R}^{20}\cong\mathbb{R}^{10}\times\mathbb{R}^{10}$ with `EuclideanSpace.finAddEquivProd` and applying the identity on the first factor and `simplexFacetLinear 9 (some i)`, which is `insertZero i`, on the second. The right-hand side is `insertZero (i.natAdd 10)`, the isometry $\iota_{10+i}$ regarded as a linear map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductFacetGraphs.lean#L58-L79

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

theorem OAI.ProjectionCounterexample.productFacetLinear_second_coordinate (i : Fin 10) :
    productFacetLinear (true, some i) = (insertZero (i.natAdd 10)).toLinearMap := by sorry

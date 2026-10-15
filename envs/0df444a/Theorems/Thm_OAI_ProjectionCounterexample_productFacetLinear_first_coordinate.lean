-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_productFacetLinear_first_coordinate
-- name    : OAI.ProjectionCounterexample.productFacetLinear_first_coordinate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:49:16.826149+00:00
-- url     : https://prove2.me/theorems/6c8bb0c8-126f-470d-8ef7-69188efc15d1
-- title:
--   First-block coordinate facet charts of $T_{10}\times T_{10}$ insert a zero coordinate
-- statement:
--   Consider the product of standard simplices $P=T_{10}\times T_{10}\subseteq\mathbb{R}^{20}$ and, for $i\in\{1,\dots,10\}$, its facet $\{x\in P:\ x_i=0\}$ on a coordinate hyperplane of the first block. The linear part $L_{(1,i)}:\mathbb{R}^{19}\to\mathbb{R}^{20}$ of the affine chart of this facet is defined blockwise: splitting $\mathbb{R}^{19}=\mathbb{R}^9\times\mathbb{R}^{10}$ and $\mathbb{R}^{20}=\mathbb{R}^{10}\times\mathbb{R}^{10}$, it is $L_{(1,i)}(z',z'')=(\iota^{(10)}_i z',\,z'')$, where $\iota^{(10)}_i:\mathbb{R}^9\to\mathbb{R}^{10}$ inserts a zero in position $i$. The statement is that this map is simply the insertion of a zero in position $i$ of $\mathbb{R}^{20}$:
--   $$
--   L_{(1,i)}(z_1,\dots,z_{19})=(z_1,\dots,z_{i-1},\,0,\,z_i,\dots,z_{19})=\iota^{(20)}_i(z).
--   $$
--
--   In particular $L_{(1,i)}$ is a linear isometry, so these ten facets of $P$ are isometric to $T_9\times T_{10}$ and their $19$-dimensional measures and shadows can be computed exactly as for coordinate facets of a simplex.
--
--   **Formalization Note** The left side is `productFacetLinear (false, some i)` and the right side is the isometry `insertZero (i.castAdd 10)` viewed as a linear map; coordinates are indexed from $0$ in Lean, and `Fin.castAdd 10` places $i$ in the first block of `Fin 20`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductFacetGraphs.lean#L35-L56

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

theorem OAI.ProjectionCounterexample.productFacetLinear_first_coordinate (i : Fin 10) :
    productFacetLinear (false, some i) = (insertZero (i.castAdd 10)).toLinearMap := by sorry

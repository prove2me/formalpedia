-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_product_facet_transverse
-- name    : OAI.ProjectionCounterexample.product_facet_transverse
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:49:00.257771+00:00
-- url     : https://prove2.me/theorems/df7273d7-1155-44f8-8c3e-196cc66bd55b
-- title:
--   Distinct facet hyperplanes of $T_{10}\times T_{10}$ cut each facet chart transversally
-- statement:
--   Let $T_m=\operatorname{conv}\{0,e_1,\dots,e_m\}\subseteq\mathbb{R}^m$ be the standard simplex and let $P=T_{10}\times T_{10}\subseteq\mathbb{R}^{20}$, writing $x=(x',x'')$ with $x'$ the first ten and $x''$ the last ten coordinates. The facets of $T_{10}$ are indexed by $k\in\{\Sigma,1,\dots,10\}$, with outward functionals $\varphi_\Sigma(y)=\sum_jy_j$, $\varphi_k(y)=-y_k$ and levels $\beta_\Sigma=1$, $\beta_k=0$. Accordingly $P$ is the intersection of $22$ halfspaces, indexed by pairs $(b,k)$ with block $b\in\{1,2\}$:
--   $$
--   \Phi_{(1,k)}(x)=\varphi_k(x')\le\beta_k,\qquad \Phi_{(2,k)}(x)=\varphi_k(x'')\le\beta_k .
--   $$
--
--   Each facet of $T_{10}$ has an affine chart $\gamma_k(z)=c_k+L_kz$ from $\mathbb{R}^9$, with $L_\Sigma(z)=(z,\,-\sum_jz_j)$, $c_\Sigma=e_{10}$ (so $\gamma_\Sigma(z)=(z,\,1-\sum_jz_j)$), and $L_k=\iota_k$ the insertion of a zero in position $k$, $c_k=0$. The product facet charts are maps $\mathbb{R}^{19}\to\mathbb{R}^{20}$ acting blockwise: for the first block, $\mathbb{R}^{19}=\mathbb{R}^9\times\mathbb{R}^{10}$ and
--   $$
--   L_{(1,k)}(z',z'')=(L_kz',\,z''),\qquad C_{(1,k)}=(c_k,0),
--   $$
--   and for the second block, $\mathbb{R}^{19}=\mathbb{R}^{10}\times\mathbb{R}^9$ and $L_{(2,k)}(z',z'')=(z',\,L_kz'')$, $C_{(2,k)}=(0,c_k)$. Then for any two distinct facet indices $(b,k)\ne(b',l)$,
--   $$
--   \Phi_{(b',l)}\circ L_{(b,k)}\ne 0
--   $$
--   as a linear functional on $\mathbb{R}^{19}$.
--
--   Thus the defining functional of any other facet is not constant along the affine hull of a given facet of $P$, so the other facet hyperplanes meet each $19$-dimensional facet chart in lower-dimensional sets. This is the hypothesis under which the pairwise intersections of the $22$ facets, and their shadows under orthogonal projection, are shown to be null for $19$-dimensional Hausdorff measure, as required to write the projection volume of $T_{10}\times T_{10}$ as a sum over visible facets.
--
--   **Formalization Note** Indices range over `Bool × Option (Fin 10)` (`false` for the first block, `none` for the slanted facet); $\Phi$ is `productFunctional` and $L_{(b,k)}$ is `productFacetLinear`, a bundled linear map `E 19 →ₗ[ℝ] E 20`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductFacetCharts.lean#L149-L181

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

open OAI OAI.ProjectionCounterexample
open Set

theorem OAI.ProjectionCounterexample.product_facet_transverse (i j : Bool × Option (Fin 10)) (hij : i ≠ j) :
    (productFunctional j).comp (productFacetLinear i) ≠ 0 := by sorry

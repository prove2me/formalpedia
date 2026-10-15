-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_product_facet_eq_affine_image
-- name    : OAI.ProjectionCounterexample.product_facet_eq_affine_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:48:45.695408+00:00
-- url     : https://prove2.me/theorems/51acf99f-d5a6-40eb-b28b-bb4c8feda89c
-- title:
--   Explicit affine parametrizations of the 22 facets of $T_{10}\times T_{10}$
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
--   and for the second block, $\mathbb{R}^{19}=\mathbb{R}^{10}\times\mathbb{R}^9$ and $L_{(2,k)}(z',z'')=(z',\,L_kz'')$, $C_{(2,k)}=(0,c_k)$. Let $D_1=T_9\times T_{10}$ and $D_2=T_{10}\times T_9$, viewed as subsets of $\mathbb{R}^{19}$ through these splittings. Then for each of the $22$ indices $(b,k)$, the face $F_{(b,k)}=\{x\in P:\ \Phi_{(b,k)}(x)=\beta_k\}$ is the affine image
--   $$
--   F_{(b,k)}=\bigl\{\,C_{(b,k)}+L_{(b,k)}z:\ z\in D_b\,\bigr\}.
--   $$
--   For instance, $F_{(1,\Sigma)}=\{(\gamma_\Sigma(z'),z''):\ z'\in T_9,\ z''\in T_{10}\}$.
--
--   These charts parametrize every facet of $P=T_{10}\times T_{10}$ by a product of two simplices of total dimension $19$, so that the $19$-dimensional measures of the facets and of their shadows can be computed from the known volumes of $T_9\times T_{10}$ and the Jacobians of the charts. This is the input to the projection-volume formula for $P$.
--
--   **Formalization Note** The facet index type is `Bool × Option (Fin 10)`, with `false` the first block and `none` the slanted facet; the functionals and levels are `productFunctional` and `productLevel`, the face is `boundingFace productFunctional productLevel i`, the domains are `productFacetDomain`, and the chart is `productFacetCenter i + productFacetLinear i x`. Blocks are split with `EuclideanSpace.finAddEquivProd`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductFacetCharts.lean#L57-L112

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

theorem OAI.ProjectionCounterexample.product_facet_eq_affine_image (i : Bool × Option (Fin 10)) :
    boundingFace productFunctional productLevel i =
      (fun x => productFacetCenter i + productFacetLinear i x) '' productFacetDomain i.1 := by sorry

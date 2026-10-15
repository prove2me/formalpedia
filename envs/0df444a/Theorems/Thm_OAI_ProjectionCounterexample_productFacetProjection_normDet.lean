-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_productFacetProjection_normDet
-- name    : OAI.ProjectionCounterexample.productFacetProjection_normDet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:56:42.079439+00:00
-- url     : https://prove2.me/theorems/9e2c6733-6da8-4b55-8d9f-2815db86045c
-- title:
--   Projected area factors of the facet charts of $T_{10}\times T_{10}$
-- statement:
--   Index the coordinates of $\mathbb{R}^d$ by $\{0,\dots,d-1\}$. Let $T_{10}\subset\mathbb{R}^{10}$ be the standard simplex and view $T_{10}\times T_{10}\subset\mathbb{R}^{20}$, with first block $x_0,\dots,x_9$ and second block $x_{10},\dots,x_{19}$. Its $22$ facets are indexed by pairs $(b,\sigma)$ with a block $b\in\{1,2\}$ and $\sigma\in\{*,0,1,\dots,9\}$, and are cut out by the outward linear functionals
--   $$
--   \varphi_{1,*}(x)=\sum_{j=0}^{9}x_j,\quad \varphi_{1,i}(x)=-x_i,\quad \varphi_{2,*}(x)=\sum_{j=0}^{9}x_{10+j},\quad \varphi_{2,i}(x)=-x_{10+i}\qquad(0\le i\le9).
--   $$
--   Each facet carries an affine chart on $\mathbb{R}^{19}$ whose linear part $\Lambda_{b,\sigma}:\mathbb{R}^{19}\to\mathbb{R}^{20}$ applies a simplex-facet map $\lambda_\sigma:\mathbb{R}^9\to\mathbb{R}^{10}$ in block $b$ and the identity in the other block,
--   $$
--   \Lambda_{1,\sigma}(z,w)=(\lambda_\sigma z,\ w)\ \ (z\in\mathbb{R}^9,\ w\in\mathbb{R}^{10}),\qquad \Lambda_{2,\sigma}(z,w)=(z,\ \lambda_\sigma w)\ \ (z\in\mathbb{R}^{10},\ w\in\mathbb{R}^{9}),
--   $$
--   where $x\in\mathbb{R}^{19}$ is split into its leading and trailing coordinates accordingly, $\lambda_i$ inserts a zero in slot $i$, and $\lambda_*(y)=(y_0,\dots,y_8,-(y_0+\dots+y_8))$. Let $u\in\mathbb{R}^{20}$ be a unit vector, $P_u$ the orthogonal projection onto $u^\perp$, and $J(A)=\sqrt{\det(A^{*}A)}$ the norm determinant (the $19$-dimensional volume factor) of a linear map $A$ on $\mathbb{R}^{19}$.
--
--   **Theorem.** For every facet index $(b,\sigma)$ and every unit vector $u\in\mathbb{R}^{20}$,
--   $$
--   J\big(P_u\circ\Lambda_{b,\sigma}\big)=|\varphi_{b,\sigma}(u)|,
--   $$
--   that is, the factor equals $|u_0+\dots+u_9|$, $|u_i|$, $|u_{10}+\dots+u_{19}|$ or $|u_{10+i}|$ for the facets $(1,*)$, $(1,i)$, $(2,*)$ and $(2,i)$ respectively.
--
--   Combined with the area formula, this expresses the $19$-dimensional measure of the orthogonal shadow of each facet of $T_{10}\times T_{10}$ as $|\varphi_{b,\sigma}(u)|$ times the volume of the facet's parameter domain. It is the input for computing the projection volumes of the product body $T_{10}\times T_{10}$, which is compared with the simplex in dimension $20$.
--
--   **Formalization Note** Facet indices are `Bool × Option (Fin 10)`, with `false`/`true` for the first/second block and `none` for the sum facet. $\Lambda_{b,\sigma}$ is `productFacetLinear`, $\varphi_{b,\sigma}$ is `productFunctional`, $P_u$ is `project u`, and $J$ is Mathlib's `LinearMap.normDet`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductFacetProjection.lean#L11-L33

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

theorem OAI.ProjectionCounterexample.productFacetProjection_normDet (i : Bool × Option (Fin 10))
    {u : E 20} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (productFacetLinear i)).normDet =
      |productFunctional i u| := by sorry

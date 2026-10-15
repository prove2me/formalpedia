-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_product_projectionVolume
-- name    : OAI.ProjectionCounterexample.product_projectionVolume
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:00:37.553251+00:00
-- url     : https://prove2.me/theorems/c471e2cd-114b-43f7-bc8a-2134a4beebb6
-- title:
--   Projection volumes of the product $T_{10}\times T_{10}$ of two corner simplices
-- statement:
--   Let $T_{10}=\operatorname{conv}\{0,e_1,\dots,e_{10}\}\subset\mathbb{R}^{10}$ be the simplex spanned by the origin and the standard basis vectors, and let $P=T_{10}\times T_{10}\subset\mathbb{R}^{20}$ be the Cartesian product: the set of $x\in\mathbb{R}^{20}$ whose first ten coordinates $x'=(x_1,\dots,x_{10})$ and last ten coordinates $x''=(x_{11},\dots,x_{20})$ both lie in $T_{10}$. Equip $\mathbb{R}^{20}$ with the standard inner product. For a unit vector $u\in\mathbb{R}^{20}$ let $\pi_u$ be the orthogonal projection of $\mathbb{R}^{20}$ onto the hyperplane $u^{\perp}$, and let $\mathcal{H}^{19}$ be the $19$-dimensional Hausdorff measure on $\mathbb{R}^{20}$, normalized so that it agrees with Lebesgue measure on $19$-dimensional affine subspaces. The projection volume (brightness) of $P$ in direction $u$ is
--   $\operatorname{vol}_{19}(P\,|\,u^{\perp})=\mathcal{H}^{19}\bigl(\pi_u(P)\bigr)$.
--
--   **Theorem.** For every $u\in\mathbb{R}^{20}$ with $\|u\|=1$, writing $u'=(u_1,\dots,u_{10})$ and $u''=(u_{11},\dots,u_{20})$ for its two blocks of coordinates,
--
--   $$
--   \operatorname{vol}_{19}\bigl(P\,|\,u^{\perp}\bigr)=\frac{\displaystyle\sum_{i=1}^{10}|u'_i|+\Bigl|\sum_{i=1}^{10}u'_i\Bigr|+\sum_{i=1}^{10}|u''_i|+\Bigl|\sum_{i=1}^{10}u''_i\Bigr|}{2\cdot 9!\cdot 10!}.
--   $$
--
--   With $h_k(v)=\tfrac12\bigl(\sum_{i=1}^{k}|v_i|+|\sum_{i=1}^{k}v_i|\bigr)$ for $v\in\mathbb{R}^k$, the support function of the centered zonotope $[-\tfrac12,\tfrac12]^{k}+[-\tfrac12,\tfrac12]\,(1,\dots,1)$, the formula says that the brightness function of $T_{10}\times T_{10}$ is $u\mapsto\bigl(h_{10}(u')+h_{10}(u'')\bigr)/(9!\,10!)$. This is exactly the input needed to identify the projection body of $T_{10}\times T_{10}$ as a product of two scaled zonotopes. That explicit body is what makes the comparison of the normalized projection-body volume $\operatorname{vol}_{20}(\Pi P)/\operatorname{vol}_{20}(P)^{19}$ of $T_{10}\times T_{10}$ with that of the $20$-dimensional simplex $\operatorname{conv}\{0,e_1,\dots,e_{20}\}$ computable, and the comparison shows that the simplex does not maximize this ratio among convex bodies in $\mathbb{R}^{20}$.
--
--   **Formalization Note** The body is `productBody` and the blocks $u',u''$ are `firstBlock u` and `secondBlock u`. The quantity `projectionVolume productBody u` is defined as the real number (`ENNReal.toReal`) obtained from `μHE[19]`, Mathlib's Euclidean Hausdorff measure, applied to the image of the body under `project u`, the orthogonal projection onto the orthogonal complement of the line $\mathbb{R}u$; the dimension $19$ arises as $20-1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductBrightness.lean#L47-L66

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
import Definitions.Def_OAI_Geometry_ProjectionBody_ProjectionKernel

open OAI OAI.ProjectionCounterexample
open Set MeasureTheory Measure

theorem OAI.ProjectionCounterexample.product_projectionVolume {u : E 20} (hu : ‖u‖ = 1) :
    projectionVolume productBody u =
      (((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) +
        ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|)) /
      (2 * ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) := by sorry

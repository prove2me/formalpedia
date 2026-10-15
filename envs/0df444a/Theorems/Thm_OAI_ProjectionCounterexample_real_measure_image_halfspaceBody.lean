-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_real_measure_image_halfspaceBody
-- name    : OAI.ProjectionCounterexample.real_measure_image_halfspaceBody
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:59:46.390724+00:00
-- url     : https://prove2.me/theorems/9b3f7d7e-6e97-4e16-9dcb-4f7b0d9220ba
-- title:
--   Shadow measure of a polyhedron from balanced facet shadows
-- statement:
--   Let $\iota$ be a finite index set, $V$ and $W$ real vector spaces, and $\mu$ a measure on a $\sigma$-algebra of $W$. Given linear functionals $a_i:V\to\mathbb{R}$ and numbers $b_i\in\mathbb{R}$ for $i\in\iota$, consider the polyhedron and its faces
--   $$
--   K=\{x\in V:\ a_i(x)\le b_i\ \text{for all }i\},\qquad F_i=\{x\in K:\ a_i(x)=b_i\}.
--   $$
--   Let $q:V\to W$ be linear, $u\in V$ and $c\in\mathbb{R}$, and assume:
--
--   1. $q(u)=0$ and $\ker q=\operatorname{span}\{u\}$, so $q$ collapses exactly the direction $u$;
--   2. $a_i(u)>0$ for at least one $i$;
--   3. every shadow $q(F_i)$ is measurable;
--   4. $\mu\big(q(F_i\cap F_j)\big)=0$ whenever $i\ne j$;
--   5. the slopes are balanced, $\sum_{i\in\iota}a_i(u)=0$;
--   6. $c\ge0$ and every facet shadow has measure $\mu(q(F_i))=c\,|a_i(u)|$.
--
--   **Theorem.** Under these hypotheses, as an identity of real numbers,
--   $$
--   \mu\big(q(K)\big)=\frac{c}{2}\sum_{i\in\iota}|a_i(u)| .
--   $$
--
--   This is an abstract shadow formula for polyhedra: it computes the measure of the shadow of $K$ along the direction $u$ from the measures of the shadows of its facets. With $q$ the orthogonal projection onto $u^\perp$, $\mu$ the $(d-1)$-dimensional Hausdorff measure on $\mathbb{R}^d$, and facet measures computed from projected facet charts, it yields the projection volumes of the simplex and of the product of two simplices.
--
--   **Formalization Note** $K$ is `halfspaceBody a b` and $F_i$ is `boundingFace a b i`. The conclusion is stated for the real number `(μ (q '' halfspaceBody a b)).toReal`, and the facet hypothesis reads `μ (q '' boundingFace a b i) = ENNReal.ofReal (c * |a i u|)`. No topology on $V$ or $W$ is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/BrightnessSum.lean#L16-L42

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
open Set MeasureTheory
variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [MeasurableSpace W]

theorem OAI.ProjectionCounterexample.real_measure_image_halfspaceBody
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W) (μ : Measure W)
    {u : V} (hqu : q u = 0) (hu : ∃ i, 0 < a i u)
    (hker : LinearMap.ker q = Submodule.span ℝ {u})
    (hmeas : ∀ i, MeasurableSet (q '' boundingFace a b i))
    (hnull : ∀ i j, i ≠ j →
      μ (q '' (boundingFace a b i ∩ boundingFace a b j)) = 0)
    (c : ℝ) (hc : 0 ≤ c) (hbalance : ∑ i, a i u = 0)
    (hfacet : ∀ i, μ (q '' boundingFace a b i) = ENNReal.ofReal (c * |a i u|)) :
    (μ (q '' halfspaceBody a b)).toReal = c * (∑ i, |a i u|) / 2 := by sorry

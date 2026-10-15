-- Prove2me | Theorems.Thm_OAI_RuledApproximation_IsParallelogram_linear_image
-- name    : OAI.RuledApproximation.IsParallelogram.linear_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:39:53.968103+00:00
-- url     : https://prove2.me/theorems/3afa5a52-3884-4e10-b1ea-11e0aaf3c870
-- title:
--   Injective linear images of parallelograms are parallelograms
-- statement:
--   Let $E$ and $F$ be real vector spaces. A subset $P\subseteq E$ is called a *parallelogram* if there are vectors $c,u,v\in E$ with $u,v$ linearly independent such that
--   $$P=\{\,c+s\,u+t\,v:\ s,t\in[0,1]\,\}.$$
--
--   **Theorem.** If $P\subseteq E$ is a parallelogram and $f:E\to F$ is an injective linear map, then the image $f(P)$ is a parallelogram in $F$:
--   $$P\ \text{a parallelogram},\quad f\ \text{linear and injective}\quad\Longrightarrow\quad f(P)\ \text{a parallelogram}.$$
--
--   In the cylinder-covering problem for ruled surfaces the admissible cylinders are those whose base, a subset of the plane orthogonal to the axis, is a parallelogram. This lemma transports that shape condition along injective linear maps. Applied to the perpendicular projection of the parameter plane onto the cross-section of a slanted cylinder (injective when the vertical scale is positive), it shows that cylinders over planar parallelograms, such as square tiles, have parallelogram bases; applied to the restriction of an orthogonal map of $\mathbb{R}^3$ to an axis-orthogonal plane, it shows that rotating a cylinder keeps its base a parallelogram.
--
--   **Formalization Note** Parallelograms are closed and non-degenerate: the edge vectors must be linearly independent, expressed as linear independence of the family `![u, v]`. The spaces $E$ and $F$ are arbitrary modules over $\mathbb{R}$; no topology, dimension or finiteness assumption is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Projection.lean#L161-L177

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.IsParallelogram.linear_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {P : Set E} (hP : IsParallelogram P) (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    IsParallelogram (f '' P) := by sorry

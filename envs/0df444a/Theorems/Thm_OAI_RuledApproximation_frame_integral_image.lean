-- Prove2me | Theorems.Thm_OAI_RuledApproximation_frame_integral_image
-- name    : OAI.RuledApproximation.frame_integral_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:41:51.621187+00:00
-- url     : https://prove2.me/theorems/0261664a-511f-49cf-b244-9d6a03324185
-- title:
--   Linear change of variables for integrals over the image of a planar set
-- statement:
--   Let $M:\mathbb{R}^2\to\mathbb{R}^2$ be an invertible linear map from the coordinate plane to the Euclidean plane, and let $J(M)=|\det M|$ be the absolute value of its determinant in the standard bases (the *frame Jacobian* of $M$). Then for every Lebesgue measurable set $K\subseteq\mathbb{R}^2$ and every function $F:\mathbb{R}^2\to\mathbb{R}$,
--   $$
--   \int_{M(K)}F(p)\,dp=J(M)\int_K F(Mx)\,dx,
--   $$
--   where both integrals are taken with respect to two-dimensional Lebesgue measure.
--
--   This is the change-of-variables formula that moves integrals between adapted linear coordinates (a frame in which the derivative of a vector field takes a normal form) and the physical plane. Taking $F\equiv1$ gives $|M(K)|=J(M)\,|K|$ for the area of the image.
--
--   **Formalization Note** $M$ is a continuous linear equivalence from `Coordinates` (the type `Fin 2 → ℝ`) to `Plane` (the type `EuclideanSpace ℝ (Fin 2)`), and `frameJacobian M` is the absolute determinant of $M$ followed by the canonical identification of `Plane` with `Fin 2 → ℝ`. No integrability assumption is made: integrals are Bochner integrals, which equal $0$ for non-integrable functions, and $F$ is integrable on $M(K)$ exactly when $F\circ M$ is integrable on $K$, so the identity also holds in that degenerate case.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Frames.lean#L21-L36

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.frame_integral_image (M : Coordinates ≃L[ℝ] Plane) {K : Set Coordinates}
    (hK : MeasurableSet K) (F : Plane → ℝ) :
    (∫ p in M '' K, F p) = frameJacobian M * (∫ x in K, F (M x)) := by sorry

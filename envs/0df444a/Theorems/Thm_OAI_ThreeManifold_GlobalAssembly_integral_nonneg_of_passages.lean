-- Prove2me | Theorems.Thm_OAI_ThreeManifold_GlobalAssembly_integral_nonneg_of_passages
-- name    : OAI.ThreeManifold.GlobalAssembly.integral_nonneg_of_passages
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:43:57.611997+00:00
-- url     : https://prove2.me/theorems/e6839d1a-44bb-4c8a-b018-bd84cc44ece2
-- title:
--   An integral over $\mathbb{R}$ is nonnegative if it is nonnegative on each component of an open set and the integrand is nonnegative off it
-- statement:
--   Let $U \subseteq \mathbb{R}$ be open and, for $x \in U$, let $\mathcal{C}_U(x)$ be the connected component of $x$ in $U$ (an open interval). All integrals are with respect to Lebesgue measure.
--
--   **Theorem.** Let $f : \mathbb{R} \to \mathbb{R}$ be Lebesgue integrable. Assume that
--   $$
--   \int_{\mathcal{C}_U(x)} f(s)\,ds \ \ge\ 0 \quad \text{for every } x \in U, \qquad\text{and}\qquad f(s) \ge 0 \quad \text{for every } s \notin U .
--   $$
--   Then
--   $$
--   \int_{\mathbb{R}} f(s)\,ds \ \ge\ 0 .
--   $$
--
--   This is the bookkeeping step that turns local estimates into a global one: if an index-form density along a geodesic is pointwise nonnegative outside the times spent in a special region, and its integral over each individual passage through that region is nonnegative, then the total index form is nonnegative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Index.lean#L1310-L1325

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index

open OAI OAI.ThreeManifold OAI.ThreeManifold.GlobalAssembly
open Set MeasureTheory Topology Function

theorem OAI.ThreeManifold.GlobalAssembly.integral_nonneg_of_passages {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : Integrable f)
    (hpass : ∀ x ∈ U, 0 ≤ ∫ s in connectedComponentIn U x, f s)
    (hoff : ∀ s ∉ U, 0 ≤ f s) : 0 ≤ ∫ s, f s := by sorry

-- Prove2me | Theorems.Thm_OAI_ThreeManifold_FinitePassage_endpoint_alternative
-- name    : OAI.ThreeManifold.FinitePassage.endpoint_alternative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:24:19.829198+00:00
-- url     : https://prove2.me/theorems/0e3e4063-e8fb-49cd-abbf-130a426c9c5e
-- title:
--   Endpoints of a maximal passage through a set are window endpoints or frontier points
-- statement:
--   Let $X$ be a topological space, $O\subseteq X$ any subset, and $\gamma:\mathbb{R}\to X$ a map that is continuous on the closed interval $[A,B]$. Let $a,b\in\mathbb{R}$ with
--   $$
--   A\le a<b\le B,\qquad \gamma\big((a,b)\big)\subseteq O,
--   $$
--   and suppose that neither $a$ nor $b$ belongs to the set $(A,B)\cap\gamma^{-1}(O)$. Then
--   $$
--   \big(a=A\ \text{ or }\ \gamma(a)\in\overline{O}\setminus O\big)\quad\text{and}\quad\big(b=B\ \text{ or }\ \gamma(b)\in\overline{O}\setminus O\big).
--   $$
--
--   Combined with the description of connected components of open subsets of $(A,B)$ as open intervals whose endpoints lie outside the set, this classifies the endpoints of a maximal time interval that a curve spends in $O$. Each endpoint is either an endpoint of the observation window $[A,B]$ or a time at which the curve sits on the frontier $\overline{O}\setminus O$. No openness of $O$ is assumed.
--
--   **Formalization Note** Continuity is only required on `Icc A B` (`ContinuousOn γ (Icc A B)`), and the hypothesis on the endpoints is literally `a ∉ Ioo A B ∩ γ ⁻¹' O` (and the same for `b`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L636-L660

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
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages

open OAI OAI.ThreeManifold
open Set Filter Topology

theorem OAI.ThreeManifold.FinitePassage.endpoint_alternative {M : Type*} [TopologicalSpace M] {O : Set M}
    {γ : ℝ → M} {A B a b : ℝ} (hab : a < b) (hAa : A ≤ a) (hbB : b ≤ B)
    (hr : ∀ s ∈ Ioo a b, γ s ∈ O)
    (hc : ContinuousOn γ (Icc A B))
    (ha : a ∉ Ioo A B ∩ γ ⁻¹' O) (hb : b ∉ Ioo A B ∩ γ ⁻¹' O) :
    (a = A ∨ γ a ∈ closure O \ O) ∧ (b = B ∨ γ b ∈ closure O \ O) := by sorry

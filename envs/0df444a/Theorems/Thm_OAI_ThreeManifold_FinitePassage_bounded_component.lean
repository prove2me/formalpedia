-- Prove2me | Theorems.Thm_OAI_ThreeManifold_FinitePassage_bounded_component
-- name    : OAI.ThreeManifold.FinitePassage.bounded_component
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:23:13.933707+00:00
-- url     : https://prove2.me/theorems/d112bb9c-7f41-4d2d-93ff-2b524925a26b
-- title:
--   Connected components of a bounded open subset of $\mathbb{R}$ are open intervals whose endpoints lie outside the set
-- statement:
--   Let $P\subseteq\mathbb{R}$ be an open set and $A,B\in\mathbb{R}$ with $P\subseteq(A,B)$. For $x\in P$, let $\operatorname{comp}_P(x)$ be the connected component of $x$ in $P$, that is, the union of all connected subsets of $P$ containing $x$.
--
--   **Theorem.** For every $x\in P$ there are real numbers $a<b$ such that
--   $$
--   A\le a,\qquad b\le B,\qquad \operatorname{comp}_P(x)=(a,b),\qquad a\notin P,\qquad b\notin P .
--   $$
--
--   In words, a bounded open subset of the line splits into maximal open intervals, and the endpoints of each such interval are not in the set. This is used to decompose the set of times at which a curve lies in a given open region into maximal "passages" with well-defined entry and exit times.
--
--   **Formalization Note** The component is Mathlib's `connectedComponentIn P x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L602-L634

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

theorem OAI.ThreeManifold.FinitePassage.bounded_component {P : Set ℝ} (hP : IsOpen P) {A B x : ℝ}
    (hPB : P ⊆ Ioo A B) (hx : x ∈ P) :
    ∃ a b : ℝ, a < b ∧ A ≤ a ∧ b ≤ B ∧
      connectedComponentIn P x = Ioo a b ∧ a ∉ P ∧ b ∉ P := by sorry

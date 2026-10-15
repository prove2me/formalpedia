-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_near_lexicographic_maximum
-- name    : OAI.DoublingHilbert.near_lexicographic_maximum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:36:39.465859+00:00
-- url     : https://prove2.me/theorems/afc1c662-9a0f-4d11-bb24-b91165e0f475
-- title:
--   Near the top fiber of a compact planar set, the second coordinate is almost bounded by its top-fiber bound
-- statement:
--   Let $K\subseteq\mathbb{R}^2$ be compact and let $A,B\in\mathbb{R}$ be such that every $p=(p_1,p_2)\in K$ satisfies $p_1\le A$, and every $p\in K$ with $p_1=A$ satisfies $p_2\le B$. Then for every $\varepsilon>0$ there is $\delta>0$ such that
--
--   $$
--   p\in K\ \text{ and }\ p_1>A-\delta\quad\Longrightarrow\quad p_2\le B+\varepsilon .
--   $$
--
--   Typically $A$ is the largest first coordinate on $K$ and $B$ the largest second coordinate among the points of $K$ with first coordinate $A$, so that $(A,B)$ is the lexicographic maximum of $K$; the lemma is an upper semicontinuity statement for the second coordinate near this top fiber. Neither nonemptiness of $K$ nor attainment of $A$ or $B$ is assumed. It is the first step towards an affine barrier for $K$, used for the compact set of squared derivative norms of a Lipschitz map in the proof that a certain doubling subset of $\ell^2$ admits no bi-Lipschitz embedding into any $\mathbb{R}^k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Extremal.lean#L11-L39

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology

theorem OAI.DoublingHilbert.near_lexicographic_maximum
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {A B : ℝ}
    (hfirst : ∀ p ∈ K, p.1 ≤ A)
    (hsecond : ∀ p ∈ K, p.1 = A → p.2 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, A - δ < p.1 → p.2 ≤ B + ε := by sorry

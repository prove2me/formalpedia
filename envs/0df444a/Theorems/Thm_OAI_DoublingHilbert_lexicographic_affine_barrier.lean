-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_lexicographic_affine_barrier
-- name    : OAI.DoublingHilbert.lexicographic_affine_barrier
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:37:05.624208+00:00
-- url     : https://prove2.me/theorems/849cc10d-10eb-481a-8a14-4f1e5fdd7940
-- title:
--   Affine barrier for a compact planar set below its lexicographic maximum
-- statement:
--   Let $K\subseteq\mathbb{R}^2$ be compact and let $A,B,M\in\mathbb{R}$ with $B\ge0$ and $M\ge0$. Assume that every $p=(p_1,p_2)\in K$ satisfies $p_1\le A$ and $p_2\le M$, and that every $p\in K$ with $p_1=A$ satisfies $p_2\le B$. Then for every $\varepsilon>0$ there is a constant $C\ge0$ such that
--
--   $$
--   p_2\le B+\varepsilon+C\,(A-p_1)\qquad\text{for all }p\in K .
--   $$
--
--   Thus $K$ lies below an affine function of the deficit $A-p_1\ge0$ whose value on the top fiber $\{p_1=A\}$ is $B+\varepsilon$. Because the bound is affine it can be integrated: if a random point of $K$ has first coordinate close to $A$ on average, its second coordinate is on average at most about $B+\varepsilon$. In the proof that a certain doubling subset of $\ell^2$ has no bi-Lipschitz embedding into any $\mathbb{R}^k$, $K$ is the compact set of pairs of squared partial-derivative norms of the embedding along the sheets, $(A,B)$ is its lexicographic maximum, and this barrier drives the estimate of the vertical energy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Extremal.lean#L58-L76

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

theorem OAI.DoublingHilbert.lexicographic_affine_barrier
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {A B M : ℝ}
    (hfirst : ∀ p ∈ K, p.1 ≤ A)
    (hsecond : ∀ p ∈ K, p.1 = A → p.2 ≤ B)
    (hbound : ∀ p ∈ K, p.2 ≤ M) (hB : 0 ≤ B) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1) := by sorry

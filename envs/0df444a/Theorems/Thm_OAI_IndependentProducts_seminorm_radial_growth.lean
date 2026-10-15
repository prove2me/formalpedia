-- Prove2me | Theorems.Thm_OAI_IndependentProducts_seminorm_radial_growth
-- name    : OAI.IndependentProducts.seminorm_radial_growth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:57:06.343544+00:00
-- url     : https://prove2.me/theorems/2e16482d-001a-4492-a7dd-0cea8351e26a
-- title:
--   A one-sided gain of a seminorm persists at all larger step sizes
-- statement:
--   Let $X$ be a real normed space, $N$ a seminorm on $X$, and $x,w\in X$ with $N(x)=1$. Let $t,r,\gamma\in\mathbb{R}$ satisfy $0<t\le r$ and $\gamma\ge0$. Then
--
--   $$N(x+tw)\ \ge\ 1+\gamma\qquad\Longrightarrow\qquad N(x+rw)\ \ge\ 1+\gamma .$$
--
--   Thus a gain of at least $\gamma$ above the unit level, obtained by moving from the $N$-unit vector $x$ by the step $t$ in the direction $w$, persists for every larger step $r$. This convexity fact lets one normalize directions in the one-sided asymptotic modulus: a lower bound for $N$-unit directions $y$ at scale $t$ transfers to all directions $z$ with $N(z)\ge t$.
--
--   **Formalization Note** $N$ is an arbitrary real seminorm on $X$ (`Seminorm`), not required to be a norm or to be comparable with the norm of $X$, and $w$ is arbitrary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean#L103-L118

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.IndependentProducts.seminorm_radial_growth (N : Seminorm ℝ X) {x w : X} (hx : N x = 1)
    {t r γ : ℝ} (ht : 0 < t) (htr : t ≤ r) (hγ : 0 ≤ γ)
    (hg : 1 + γ ≤ N (x + t • w)) : 1 + γ ≤ N (x + r • w) := by sorry

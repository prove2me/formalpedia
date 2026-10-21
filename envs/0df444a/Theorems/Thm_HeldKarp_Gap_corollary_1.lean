-- Prove2me | Theorems.Thm_HeldKarp_Gap_corollary_1
-- name    : HeldKarp.Gap.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:04.02788+00:00
-- url     : https://prove2.me/theorems/ac423013-a5bb-428b-b0a1-99c349335237
-- title:
--   Corollary 1 — the gap $f(\pi)$ vanishes for some $\pi$ iff the linear program (4) has an integral optimal solution
-- statement:
--   Let $n\ge 3$ and let $c_{ij}$ be arbitrary real weights on the edges of the complete graph $K_n$. For $\pi\in\mathbb R^n$ let $f(\pi)$ be the gap: the weight of a minimum tour minus the weight of a minimum 1-tree, both with respect to the weights $c_{ij}+\pi_i+\pi_j$. Let (4) be the linear program
--
--   $$
--   v=\min_x\{cx\mid Ax=b,\ A'x\le b',\ x\ge 0\},
--   $$
--
--   over real $\binom n2$-vectors $x$, with constraints: degree $2$ at the vertices $2,\dots,n-1$; $\sum_j x_{1j}=2$; $\sum_{i<j}x_{ij}=n$; $\sum_{i\in S,\,j\in S,\,i<j}x_{ij}\le|S|-1$ for every nonempty proper subset $S\subset\{2,\dots,n\}$; $0\le x_{ij}\le 1$. Then
--
--   $$
--   \big(\exists\,\pi\in\mathbb R^n:\ f(\pi)=0\big)\iff \big(\text{(4) has an optimal solution } \bar x \text{ with every } \bar x_{ij}\in\mathbb Z\big).
--   $$
--
--   Equivalently, the Held–Karp lower bound $\max_\pi w(\pi)$ equals the optimal tour weight exactly when the subtour linear program has an integral optimum.
--
--   **Formalization Note** $\bar x$ is optimal among all real feasible points of (4), and "integer" means every coordinate is an integer. $\sum_j x_{1j}=2$ and $\sum x_{ij}=n$ are equalities as printed in (3′), and subsets $S$ are nonempty. The gap is taken over all $\pi\in\mathbb R^n$, not over the normalized $\bar\pi$. Vertices are `Fin n` (vertex $1$ is `0`, vertex $n$ is `lastV n`); $3\le n$ is the paper's standing setting, without which there are no tours or 1-trees.
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, p. 1145, §2, Corollary 1 (and the Abstract, p. 1138)

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
import Definitions.Def_HeldKarp_Gap_GapFunction
import Definitions.Def_HeldKarp_Gap_SubtourLP

open Classical
open HeldKarp.Ascent

namespace HeldKarp.Gap

/-- **Corollary 1** (Held & Karp 1970, §2, p. 1145). The gap `f(π)` assumes the value zero for
some `π` if and only if the linear program (4) has an optimal solution `x̄` such that `x̄` is
integer. -/
theorem corollary_1 {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) :
    (∃ π : Fin n → ℝ, gap c π = 0) ↔
      ∃ x : Edge n → ℝ, IsOptimal4 c x ∧ ∀ e : Edge n, ∃ z : ℤ, x e = z := by sorry

end HeldKarp.Gap

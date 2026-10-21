-- Prove2me | Theorems.Thm_HeldKarp_Gap_theorem_2
-- name    : HeldKarp.Gap.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:31.036883+00:00
-- url     : https://prove2.me/theorems/cacf918a-793f-4df3-a946-2e1dfebc0094
-- title:
--   Theorem 2 — $\max_\pi w(\pi)$ equals the value $v$ of the linear program (4)
-- statement:
--   Let $n\ge 3$ and let $c_{ij}$ be real edge weights on $K_n$. Let $w(\pi)=\min_k[c_k+\sum_{i=1}^n\pi_i(d_{ik}-2)]$, the minimum over the 1-trees $k$ of $K_n$, for $\pi\in\mathbb R^n$. Then
--
--   $$
--   \max_{\pi\in\mathbb R^n} w(\pi)=v,\qquad\text{where}\qquad v=\min_x\{cx\mid Ax=b,\ A'x\le b',\ x\ge 0\}\quad(4),
--   $$
--
--   and both the maximum and the minimum are attained. Here (4) is the linear program with constraints (i)–(vi) of (3′): degree $2$ at the vertices $2,\dots,n-1$, $\sum_j x_{1j}=2$, $\sum_{i<j}x_{ij}=n$, the subtour constraints for nonempty proper $S\subset\{2,\dots,n\}$, and $0\le x_{ij}\le 1$.
--
--   The best lower bound on the optimal tour weight obtainable from 1-trees is therefore the optimal value of the subtour linear program.
--
--   **Formalization Note** The statement asserts that some real $v$ is the least value of $cx$ over the feasible region of (4) and the greatest value of $w$ over all of $\mathbb R^n$. $\sum_j x_{1j}=2$ and $\sum x_{ij}=n$ are equalities as printed in (3′) (read literally as $\le$, the statement fails for $n=3$); subsets $S$ are nonempty. $w$ is the published `HeldKarp.Ascent.oneTreeBound`.
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, p. 1145, §2, Theorem 2 (program (4))

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
import Definitions.Def_HeldKarp_Gap_SubtourLP

open Classical
open HeldKarp.Ascent

namespace HeldKarp.Gap

/-- **Theorem 2** (Held & Karp 1970, §2, p. 1145). `max_π w(π) = v`, where
`v = min_x {cx | Ax = b, A′x ≤ b′, x ≥ 0}` is the value of the linear program (4): both the
minimum of (4) and the maximum of `w` over all real `n`-vectors `π` are attained, and they are
equal. -/
theorem theorem_2 {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) :
    ∃ v : ℝ, IsLeast (cost c '' LP4Feasible n) v ∧
      IsGreatest (Set.range (oneTreeBound c)) v := by sorry

end HeldKarp.Gap

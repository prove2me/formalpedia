-- Prove2me | Theorems.Thm_HeldKarp_Ascent_eq_2
-- name    : HeldKarp.Ascent.eq_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T06:12:45.404603+00:00
-- url     : https://prove2.me/theorems/6b2cc110-3884-451c-ae57-b58ecf8643fd
-- title:
--   Eq. (2): $C^* \ge w(\pi)$ — every 1-tree bound is below the optimum tour weight
-- statement:
--   Let $n \ge 3$, let $(c_{ij})$ be arbitrary symmetric real edge weights on $K_n$, and let $w(\pi) = \min_k [c_k + \pi\cdot v_k]$ be the 1-tree bound. Then for every real $n$-vector $\pi$ and every tour $H$ of $K_n$,
--   $$w(\pi) \le c(H).$$
--   Equivalently, with $C^*$ the weight of a minimum tour,
--   $$C^* \ge w(\pi) \quad \text{for every } \pi \in \mathbb R^n.$$
--
--   This is the family of lower bounds on which the whole method rests: the best such bound is $\max_\pi w(\pi)$, and in particular $w$ is bounded above, so its maximum exists.
--
--   **Formalization Note** $C^*$ is not named; the statement quantifies over every tour instead, which is equivalent. No metric assumption is made on the weights. The hypothesis $n \ge 3$ is implicit in the paper (for $n \le 2$ there are no tours and no 1-trees).
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, §1, p. 8 (PDF p. 3), Eq. (1) and Eq. (2)

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound

namespace HeldKarp.Ascent

/-- **Eq. (2)** (with Eq. (1)) — Held & Karp, *The traveling-salesman problem and minimum spanning
trees: Part II*, Math. Programming 1 (1971), §1, p. 8 (PDF p. 3): "C* ≥ w(π)", where C* is the
weight of a minimum tour with respect to the weights `c_ij` and
`w(π) = min_k [c_k + π · v_k]` is the minimum over 1-trees.

For `n ≥ 3`, arbitrary real edge weights `c`, every real `n`-vector `π` and every tour `H`,
`w(π) ≤ weight c H`. Since this holds for every tour, it is `C* ≥ w(π)`.

Formalization Note: `C*` is not named; quantifying over every tour is equivalent (for `n ≥ 3`
tours exist, finitely many). `3 ≤ n` is implicit in the paper: for `n ≤ 2` there is neither a
tour nor a 1-tree. Weights are arbitrary reals; no metric assumption. -/
theorem eq_2 {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (H : SimpleGraph (Fin n)) (hH : IsTour H) :
    oneTreeBound c π ≤ weight c H := by sorry

end HeldKarp.Ascent

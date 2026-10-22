-- Prove2me | Theorems.Thm_HeldKarp_Gap_gap_eq
-- name    : HeldKarp.Gap.gap_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:58.328559+00:00
-- url     : https://prove2.me/theorems/841909c2-27dd-4f37-9613-475e896a0029
-- title:
--   §1, p. 1141 — the gap is $f(\pi)=W-w(\pi)$
-- statement:
--   Let $n\ge 3$, let $c_{ij}$ be real weights on the edges of $K_n$, and let $\pi\in\mathbb R^n$. Index the 1-trees of $K_n$ by $k=1,\dots,q$; let $c_k$ be the weight of the $k$-th 1-tree with respect to $c$, and $d_{ik}$ the degree of vertex $i$ in it. Let $W$ be the weight of a minimum tour with respect to $c$, let $f(\pi)$ be the gap function (minimum tour weight minus minimum 1-tree weight, both under the weights $c_{ij}+\pi_i+\pi_j$), and let
--
--   $$
--   w(\pi)=\min_k\Big[c_k+\sum_{i=1}^n \pi_i\,(d_{ik}-2)\Big].
--   $$
--
--   Then
--
--   $$
--   f(\pi)=W+2\sum_{i=1}^n\pi_i-\min_k\Big[c_k+\sum_{i=1}^n\pi_i d_{ik}\Big]
--   \qquad\text{and}\qquad
--   f(\pi)=W-w(\pi).
--   $$
--
--   Consequently, minimizing the gap over $\pi$ is the same problem as maximizing the lower bound $w(\pi)$ on the optimal tour weight.
--
--   **Formalization Note** $w(\pi)$ is the published `HeldKarp.Ascent.oneTreeBound`, an infimum over the finite, nonempty (as $n\ge 3$) set of 1-trees; the first minimum is written the same way. The gap is defined from the transformed weights, so both identities carry content. Vertices are `Fin n`, vertex $1$ is `0`.
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, p. 1141, §1 — f(π) = W + 2Σπ_i − min_k[c_k + Σπ_i d_ik] = W − w(π)

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
import Definitions.Def_HeldKarp_Gap_GapFunction

open Classical
open HeldKarp.Ascent

namespace HeldKarp.Gap

/-- **§1, p. 1141 — the gap as `W − w(π)`** (Held & Karp 1970). For every real `n`-vector `π`,
`f(π) = W + 2 Σ_i π_i − min_k [c_k + Σ_i π_i d_ik]` and `f(π) = W − w(π)`, where `W` is the weight
of a minimum tour, `c_k` the weight and `d_ik` the degree of vertex `i` in the `k`-th 1-tree, and
`w(π) = min_k [c_k + Σ_i π_i (d_ik − 2)]` (`oneTreeBound`). -/
theorem gap_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ) :
    gap c π = tourMin c + 2 * ∑ i, π i -
        sInf {t : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧
          t = weight c G + ∑ i, π i * (G.degree i : ℝ)} ∧
      gap c π = tourMin c - oneTreeBound c π := by sorry

end HeldKarp.Gap

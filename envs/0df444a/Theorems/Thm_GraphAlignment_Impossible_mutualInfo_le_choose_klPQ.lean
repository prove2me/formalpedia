-- Prove2me | Theorems.Thm_GraphAlignment_Impossible_mutualInfo_le_choose_klPQ
-- name    : GraphAlignment.Impossible.mutualInfo_le_choose_klPQ
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:41.405223+00:00
-- url     : https://prove2.me/theorems/5cc6f9b8-da1f-4321-b349-b78f128244f5
-- title:
--   §3.2, p. 13, display after (8) — I(π*; (A, B)) ≤ C(n, 2)·D(P‖Q)
-- statement:
--   In the correlated Erdős–Rényi model $(n,q,s)$ with $0\le q<s\le1$ and $\pi^*$ uniform on the $n!$ permutations, the information the observed graphs carry about the planted permutation is at most the number of vertex pairs times the per-pair divergence:
--   $$
--   I(\pi^*;(A,B))\;\le\;\binom n2\,D(P\|Q),
--   $$
--   where $P$ and $Q$ are the edge-pair laws (3) and (4).
--
--   Combined with Corollary 3.2 and Proposition 3.3, this reduces the impossibility theorem to comparing $\binom n2 D(P\|Q)$ with $\log(M/M_\alpha)$.
--
--   **Formalization Note** Natural logarithm; $D(P\|Q)=\sum_{x\in\{0,1\}^2}P(x)\log(P(x)/Q(x))$.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 13, §3.2, display after (8)

import Mathlib
import Definitions.Def_GraphAlignment_Impossible_Setting

namespace GraphAlignment.Impossible

theorem mutualInfo_le_choose_klPQ (n : ℕ) (q s : ℝ) (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1) :
    mutualInfo (jointObs (n := n) q s) ≤ (n.choose 2 : ℝ) * klPQ q s := by sorry

end GraphAlignment.Impossible

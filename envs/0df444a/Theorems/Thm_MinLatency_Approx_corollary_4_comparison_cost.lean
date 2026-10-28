-- Prove2me | Theorems.Thm_MinLatency_Approx_corollary_4_comparison_cost
-- name    : MinLatency.Approx.corollary_4_comparison_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:12.226385+00:00
-- url     : https://prove2.me/theorems/b6aada06-ddfc-418e-85b1-aaed485e350b
-- title:
--   Proof of Corollary 4, p. 6 — with penalty 2L/k, a tour of length ≤ L missing ≤ k points has prize-collecting cost ≤ 3L
-- statement:
--   Let $V$ be a finite set of points with a distance function $d$, and let $p\in V$. Let $L\ge 0$ and let $k\ge 1$ be an integer. Place the penalty $P=2L/k$ on every point. If $T$ is a tour rooted at $p$ of closed length at most $L$ that misses at most $k$ points, then its prize-collecting cost satisfies
--
--   $$
--   \mathrm{len}(T)+\sum_{v\notin T}P\;\le\;3L .
--   $$
--
--   This is the first step of the proof of Corollary 4: with $k=\varepsilon n$ the number of points missed by the comparison tour, the penalty $P=2L/(\varepsilon n)$ makes that tour cost at most $L+\varepsilon nP=3L$, which the factor-2 prize-collecting oracle then exploits.
--
--   **Formalization Note** The miss count is the integer $k=\varepsilon n\ge 1$; the case $\varepsilon=0$ uses a different penalty in the algorithm.
--
--   Differences from the source:
--   - generalization: the comparison tour misses exactly εn points and P = 2L/(εn) → the tour misses at most k points, k ≥ 1, and P = 2L/k; reason: the cost only decreases when fewer points are missed; k = εn gives the page's statement
--   - generalization: a tour in a metric space (§3.2) → any distance function d, no metric hypothesis; reason: the bound uses no property of d; the page's metric case is a special case
--   - encoding: ε > 0 a fraction, L a tour length → k ≥ 1 a natural number with k = εn, and 0 ≤ L; reason: P = 2L/(εn) is defined exactly when εn ≥ 1; a length budget is nonnegative
--   - reading: a tour starting at p (Definition and prize-collecting problem, p. 6) → IsRootedTour p T: a duplicate-free list with head p, closed by the return leg to p (tourLen); reason: a TSP tour visits each of its points once and returns to its start; the GW algorithm returns such a tour, and under the triangle inequality any closed walk from p shortcuts to one that is no longer and visits the same points, so no instance of the page changes
-- source:
--   Blum, Chalasani, Coppersmith, Pulleyblank, Raghavan, Sudan, The Minimum Latency Problem, STOC 1994 (authors' copy, sha256 7b3a41fd…3498), PDF p. 6, proof of Corollary 4, 'So, there exists a tour of total penalty at most L + εnP = 3L in the prize-collecting sense.'

import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

namespace MinLatency.Approx

theorem corollary_4_comparison_cost {V : Type} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ) (p : V) (L : ℝ) (hL : 0 ≤ L) (k : ℕ) (hk : 1 ≤ k)
    (T : List V) (hT : IsRootedTour p T) (hlen : tourLen d T ≤ L) (hmiss : missed T ≤ k) :
    pcCost d (fun _ => 2 * L / k) T ≤ 3 * L := by sorry

end MinLatency.Approx

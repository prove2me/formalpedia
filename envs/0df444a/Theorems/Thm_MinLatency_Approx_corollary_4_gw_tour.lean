-- Prove2me | Theorems.Thm_MinLatency_Approx_corollary_4_gw_tour
-- name    : MinLatency.Approx.corollary_4_gw_tour
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:10.329409+00:00
-- url     : https://prove2.me/theorems/112c1f84-5d6a-403b-ae80-0fd0000cbe6b
-- title:
--   Proof of Corollary 4, p. 6 — the factor-2 prize-collecting oracle with penalty 2L/k returns a tour of length ≤ 6L missing ≤ 3k points
-- statement:
--   Let $d$ be a metric on a finite set $V$ and $p\in V$, and let $O$ be an admissible prize-collecting oracle: for every nonnegative penalty vector $\pi$, $O(\pi)$ is a tour rooted at $p$ whose prize-collecting cost is at most twice that of every tour rooted at $p$. Let $L>0$ and let $k\ge 1$ be an integer, and suppose some tour rooted at $p$ has closed length at most $L$ and misses at most $k$ points. Then, for the constant penalty $P=2L/k$, the tour $T=O(P)$ is rooted at $p$ and
--
--   $$
--   \mathrm{len}(T)\le 6L,\qquad \mathrm{missed}(T)\le 3k .
--   $$
--
--   In the page's terms ($k=\varepsilon n$): the GW algorithm finds a tour starting at $p$ that visits at least a $(1-3\varepsilon)$ fraction of the points and has total distance at most $6L$. This is the core of Corollary 4: one oracle call, with the right penalty, already acts as a $(3,6)$-TSP-approximator when $\varepsilon$ is known.
--
--   **Formalization Note** Lemma 3 (Goemans–Williamson) is cited, not proved, in the paper, so its guarantee is a hypothesis on the oracle, at factor $2$, the factor the proof of Corollary 4 uses.
--
--   Differences from the source:
--   - reading: the GW algorithm of Lemma 3 ([8], cited, not proved in the paper) → an arbitrary oracle O : (V → ℝ) → List V satisfying PCAdmissible d p O; reason: Lemma 3 is cited; its guarantee enters as the property of the subroutine, and the statement holds for every such subroutine
--   - generalization: a (2 − 1/(n−1))-approximation (Lemma 3) → a factor-2 guarantee (PCAdmissible); reason: the proof of Corollary 4 uses factor 2 (p. 6: 'from a 2-approximation algorithm'); every (2 − 1/(n−1))-approximate oracle is factor-2 admissible, so the statement specializes to Lemma 3's oracle
--   - generalization: the comparison tour misses exactly εn points → it misses at most k points, k ≥ 1; reason: fewer missed points only lower the comparison cost; k = εn gives the page's statement
--   - reading: of total distance 6L → closed length at most 6L; reason: the page's bound comes from cost ≤ 2·3L, an upper bound
--   - reading: bounds L of the Definition (p. 6) → 0 < L; reason: L is a tour-length budget; at L = 0 the page's penalty P = 2L/(εn) is 0 and its argument ('else the penalty is more than 6L') is void; Lemma 5 calls the approximator only with L = 2^{j+1}δ > 0
--   - reading: the distances satisfy the triangle inequality / an n-point metric space (§3.2, p. 6) → IsMetric d: symmetric, zero diagonal, positive between distinct points, triangle inequality; reason: positivity is §3.2's standing assumption (metric spaces; the proof of Lemma 5 normalises the nearest-neighbour distance to 1); without it the algorithm fails: p and z_1, …, z_m at mutual distance 0 and f at distance 1 from all of them give δ = 0, and even with δ repaired to 1 a factor-2 oracle may return (p, f, z_1, …, z_m) at L = 2, with latency 1 + 2m against 1 for (p, z_1, …, z_m, f)
--   - reading: a tour starting at p (Definition and prize-collecting problem, p. 6) → IsRootedTour p T: a duplicate-free list with head p, closed by the return leg to p (tourLen); reason: a TSP tour visits each of its points once and returns to its start; the GW algorithm returns such a tour, and under the triangle inequality any closed walk from p shortcuts to one that is no longer and visits the same points, so no instance of the page changes
-- source:
--   Blum, Chalasani, Coppersmith, Pulleyblank, Raghavan, Sudan, The Minimum Latency Problem, STOC 1994 (authors' copy, sha256 7b3a41fd…3498), PDF p. 6, proof of Corollary 4, 'Therefore, the GW algorithm finds a tour starting at the point p, that visits at least a (1 − 3ε) fraction of the vertices (else the penalty is more than 3εnP = 6L) and of total distance 6L.'

import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

namespace MinLatency.Approx

theorem corollary_4_gw_tour {V : Type} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ) (p : V) (hd : IsMetric d) (O : (V → ℝ) → List V) (hO : PCAdmissible d p O)
    (L : ℝ) (hL : 0 < L) (k : ℕ) (hk : 1 ≤ k)
    (hex : ∃ T, IsRootedTour p T ∧ tourLen d T ≤ L ∧ missed T ≤ k) :
    IsRootedTour p (O (fun _ => 2 * L / k)) ∧
      tourLen d (O (fun _ => 2 * L / k)) ≤ 6 * L ∧
      missed (O (fun _ => 2 * L / k)) ≤ 3 * k := by sorry

end MinLatency.Approx

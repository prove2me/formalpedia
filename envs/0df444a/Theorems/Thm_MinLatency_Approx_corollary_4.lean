-- Prove2me | Theorems.Thm_MinLatency_Approx_corollary_4
-- name    : MinLatency.Approx.corollary_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:20.924286+00:00
-- url     : https://prove2.me/theorems/2431cbb1-d5ff-4ec0-8228-f3a011590a5b
-- title:
--   Corollary 4, p. 6 — the scan over miss counts with any factor-2 prize-collecting oracle is a (3, 6)-TSP-approximator
-- statement:
--   Let $d$ be a metric on a finite set $V$, let $p\in V$, and let $O$ be an admissible (factor-2) prize-collecting oracle for $(d,p)$. Then the approximator $\mathrm{cor4}$ built from $O$ — for a bound $L$, call $O$ with the constant penalty $P_k(L)$ ($P_k(L)=2L/k$ for $k\ge1$, $P_0(L)=4L$) for every $k=0,1,\dots,|V|-1$, and among the returned tours of closed length at most $6L$ return one visiting the most points — is a $(3,6)$-TSP-approximator:
--
--   $$
--   \forall L>0,\ \forall k\in\mathbb N:\quad \exists T \text{ rooted at } p,\ \mathrm{len}(T)\le L,\ \mathrm{missed}(T)\le k\ \Longrightarrow\ \mathrm{cor4}(L)\text{ is rooted at }p,\ \mathrm{len}(\mathrm{cor4}(L))\le 6L,\ \mathrm{missed}(\mathrm{cor4}(L))\le 3k .
--   $$
--
--   This is the paper's Corollary 4, "There exists a $(3,6)$-TSP-approximator", with the approximator constructed from the prize-collecting subroutine of Lemma 3 as in the page's proof. It is the subroutine of the $144$-approximation (Theorem 6).
--
--   **Formalization Note** The page selects among tours "found by binary search" over $\varepsilon$; a binary search needs a monotonicity that an arbitrary factor-2 oracle does not provide, so every miss count is tried, and the page's selection rule (most points among tours of length at most $6L$) is kept.
--
--   Differences from the source:
--   - reading: There exists a (3, 6)-TSP-approximator → the specific approximator cor4Approx d p O, for every admissible oracle O, is one; reason: the page's proof constructs the approximator from the subroutine of Lemma 3; the existence is relative to that cited subroutine
--   - reading: the GW algorithm of Lemma 3 ([8], cited, not proved in the paper) → an arbitrary oracle O : (V → ℝ) → List V satisfying PCAdmissible d p O; reason: Lemma 3 is cited; its guarantee enters as the property of the subroutine, and the statement holds for every such subroutine
--   - generalization: a (2 − 1/(n−1))-approximation (Lemma 3) → a factor-2 guarantee (PCAdmissible); reason: the proof of Corollary 4 uses factor 2 (p. 6: 'from a 2-approximation algorithm'); every (2 − 1/(n−1))-approximate oracle is factor-2 admissible, so the statement specializes to Lemma 3's oracle
--   - reading: 'If ε is not known then just perform binary search, selecting the tour found of length less than 6L that visits the most vertices' → scan every miss count k = 0, …, |V| − 1 (ε = k/n), keep the tours of closed length ≤ 6L, return one visiting the most points (ties to the smallest k), fallback (p); reason: binary search needs a monotonicity in ε that an arbitrary factor-2 oracle does not give; the scan keeps the selection rule; 'less than 6L' is read as at most, the bound the oracle gives
--   - reading: P = 2L/(εn), undefined at ε = 0 → P = 4L when k = 0; reason: any P > 2L forces a factor-2 answer to miss nothing; Lean's 2L/0 = 0 would let the oracle return (p)
--   - reading: an approximator given ε and L, visiting at least (1 − αε)n vertices if a tour of length L visits (1 − ε)n vertices (Definition and Comment, p. 6) → IsTSPApprox: A is called with L only and, for every k, if some rooted tour of closed length ≤ L misses ≤ k points then A L is a rooted tour of closed length ≤ βL missing ≤ αk points; reason: the Comment allows calling the approximator with L only, and Lemma 5 does so; εn = k is the number of missed points; 'a tour of length L' is read as closed length at most L
--   - reading: bounds L of the Definition (p. 6) → 0 < L; reason: L is a tour-length budget; at L = 0 the page's penalty P = 2L/(εn) is 0 and its argument ('else the penalty is more than 6L') is void; Lemma 5 calls the approximator only with L = 2^{j+1}δ > 0
--   - reading: the distances satisfy the triangle inequality / an n-point metric space (§3.2, p. 6) → IsMetric d: symmetric, zero diagonal, positive between distinct points, triangle inequality; reason: positivity is §3.2's standing assumption (metric spaces; the proof of Lemma 5 normalises the nearest-neighbour distance to 1); without it the algorithm fails: p and z_1, …, z_m at mutual distance 0 and f at distance 1 from all of them give δ = 0, and even with δ repaired to 1 a factor-2 oracle may return (p, f, z_1, …, z_m) at L = 2, with latency 1 + 2m against 1 for (p, z_1, …, z_m, f)
--   - reading: a tour starting at p (Definition and prize-collecting problem, p. 6) → IsRootedTour p T: a duplicate-free list with head p, closed by the return leg to p (tourLen); reason: a TSP tour visits each of its points once and returns to its start; the GW algorithm returns such a tour, and under the triangle inequality any closed walk from p shortcuts to one that is no longer and visits the same points, so no instance of the page changes
-- source:
--   Blum, Chalasani, Coppersmith, Pulleyblank, Raghavan, Sudan, The Minimum Latency Problem, STOC 1994 (authors' copy, sha256 7b3a41fd…3498), PDF p. 6, Corollary 4 and its proof

import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

namespace MinLatency.Approx

theorem corollary_4 {V : Type} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ) (p : V) (hd : IsMetric d) (O : (V → ℝ) → List V)
    (hO : PCAdmissible d p O) :
    IsTSPApprox d p 3 6 (cor4Approx d p O) := by sorry

end MinLatency.Approx

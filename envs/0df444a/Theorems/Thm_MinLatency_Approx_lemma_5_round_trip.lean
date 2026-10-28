-- Prove2me | Theorems.Thm_MinLatency_Approx_lemma_5_round_trip
-- name    : MinLatency.Approx.lemma_5_round_trip
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:14.519993+00:00
-- url     : https://prove2.me/theorems/15a7d4a3-61af-4a6f-828c-57ef503ebc78
-- title:
--   Proof of Lemma 5, p. 7 — after round trip j, all but α·#{latency > 2^jδ} points are visited, each with latency ≤ β2^{j+2}δ
-- statement:
--   Let $d$ be a metric on a finite set $V$ with $n=|V|$, let $p\in V$, let $\delta$ be the distance from $p$ to its nearest neighbour, and let $A$ be an $(\alpha,\beta)$-TSP-approximator for $(d,p)$. Write $T_i=A(2^{i+1}\delta)$ for the $i$th round trip and $W_J=T_0T_1\cdots T_J$ for the walk after round trip $J$. Let $\sigma$ be any walk from $p$ visiting every point, and write $t_\sigma(v)$ for the latency of $v$ in $\sigma$. Then for all $j\le J$:
--
--   1. (coverage) the number of points visited by $T_0,\dots,T_j$ satisfies
--   $$
--   \#\{v : v\in T_i \text{ for some } i\le j\}\;\ge\; n-\alpha\cdot\#\{v : t_\sigma(v)>2^j\delta\};
--   $$
--   2. (latency) every point $v$ visited by $T_0,\dots,T_j$ has latency in $W_J$ at most
--   $$
--   \beta\, 2^{j+2}\,\delta .
--   $$
--
--   This is the step of the proof of Lemma 5 that charges the points of the algorithm's walk against the optimal one: when only few points of the optimal walk have latency above $2^j\delta$, the $j$th round trip has already visited all but $\alpha$ times as many points, and those points were reached within $\beta(2\cdot 2^j+2\cdot 2^{j-1}+\cdots)\delta\le\beta 2^{j+2}\delta$.
--
--   **Formalization Note** The page assumes $\delta=1$ "for simplicity of presentation"; here $\delta$ is explicit, and round trip $j$ uses the budget $2^{j+1}\delta$, the page's $L=2,4,8,\dots$.
--
--   Differences from the source:
--   - encoding: the nearest-neighbour distance is normalised to 1; budgets L = 2, 4, 8, …; bound β2^{j+2} → δ = nnDist d p explicit; budgets 2^{j+1}δ; bound β·2^{j+2}·δ; reason: scaling all distances by 1/δ gives the page's normalised statement
--   - reading: the blocks B_i of α vertices of our tour and the set S_j of optimal vertices of latency between 2^{j−1} and 2^j, with 'the n − ith vertex visited by the optimal tour' in S_j and i = (1 − ε)n → coverage clause: the points visited by round trips 0, …, j number at least n − α·#{v : t_σ(v) > 2^jδ}; reason: the page's indices do not parse literally; the clause is the sentence's content: when at most m optimal points have latency above 2^jδ, all but αm points are visited by round trip j
--   - reading: visited by our jth round trip → visited by one of the round trips 0, …, j; reason: the latency bound β(2∗2^j + 2∗2^{j−1} + ⋯) sums the round trips 0, …, j
--   - generalization: the minimum latency tour → any walk σ from p that visits every point; reason: the statement holds for every covering walk, in particular for an optimal one
--   - generalization: α, β are the ratios of an approximator (implicitly α, β ≥ 1) → α, β arbitrary reals, no sign hypothesis; reason: specializes to α, β ≥ 1; for α ≤ 0 or β < 0 on two or more points no approximator exists, and one point has latency 0
--   - reading: an approximator given ε and L, visiting at least (1 − αε)n vertices if a tour of length L visits (1 − ε)n vertices (Definition and Comment, p. 6) → IsTSPApprox: A is called with L only and, for every k, if some rooted tour of closed length ≤ L misses ≤ k points then A L is a rooted tour of closed length ≤ βL missing ≤ αk points; reason: the Comment allows calling the approximator with L only, and Lemma 5 does so; εn = k is the number of missed points; 'a tour of length L' is read as closed length at most L
--   - reading: bounds L of the Definition (p. 6) → 0 < L; reason: L is a tour-length budget; at L = 0 the page's penalty P = 2L/(εn) is 0 and its argument ('else the penalty is more than 6L') is void; Lemma 5 calls the approximator only with L = 2^{j+1}δ > 0
--   - reading: the distances satisfy the triangle inequality / an n-point metric space (§3.2, p. 6) → IsMetric d: symmetric, zero diagonal, positive between distinct points, triangle inequality; reason: positivity is §3.2's standing assumption (metric spaces; the proof of Lemma 5 normalises the nearest-neighbour distance to 1); without it the algorithm fails: p and z_1, …, z_m at mutual distance 0 and f at distance 1 from all of them give δ = 0, and even with δ repaired to 1 a factor-2 oracle may return (p, f, z_1, …, z_m) at L = 2, with latency 1 + 2m against 1 for (p, z_1, …, z_m, f)
--   - reading: a tour starting at p (Definition and prize-collecting problem, p. 6) → IsRootedTour p T: a duplicate-free list with head p, closed by the return leg to p (tourLen); reason: a TSP tour visits each of its points once and returns to its start; the GW algorithm returns such a tour, and under the triangle inequality any closed walk from p shortcuts to one that is no longer and visits the same points, so no instance of the page changes
-- source:
--   Blum, Chalasani, Coppersmith, Pulleyblank, Raghavan, Sudan, The Minimum Latency Problem, STOC 1994 (authors' copy, sha256 7b3a41fd…3498), PDF p. 7, proof of Lemma 5, 'All these vertices must have been visited by our jth round trip, and thus the latency in our tour for each of these vertices is bounded by β(2∗2^j + 2∗2^{j−1} + ···) ≤ β2^{j+2}.'

import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

namespace MinLatency.Approx

theorem lemma_5_round_trip {V : Type} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ) (p : V) (hd : IsMetric d) (α β : ℝ) (A : ℝ → List V)
    (hA : IsTSPApprox d p α β A) (σ : List V) (hσ : IsCoveringWalk p σ)
    (j J : ℕ) (hjJ : j ≤ J) :
    (Fintype.card V : ℝ) - α * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ)
        ≤ ((Finset.univ.filter (fun v => ∃ i ≤ j, v ∈ A (budget d p i))).card : ℝ) ∧
      ∀ v, (∃ i ≤ j, v ∈ A (budget d p i)) →
        firstVisit d (doublingWalk d p A J) v ≤ β * (2 : ℝ) ^ (j + 2) * nnDist d p := by sorry

end MinLatency.Approx

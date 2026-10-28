-- Prove2me | Theorems.Thm_MinLatency_Approx_lemma_5
-- name    : MinLatency.Approx.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:10.784439+00:00
-- url     : https://prove2.me/theorems/d7d9954a-ddf2-41e7-b099-f3819ac15dbf
-- title:
--   Lemma 5, p. 6 — doubling over any (α, β)-TSP-approximator gives latency ≤ 8⌈α⌉β times optimal with polynomially many calls
-- statement:
--   Let $d$ be a metric on a finite set $V$, let $p\in V$, let $\delta$ be the distance from $p$ to its nearest neighbour, and let $A$ be an $(\alpha,\beta)$-TSP-approximator for $(d,p)$. Run the doubling algorithm: round trip $j=0,1,2,\dots$ is $T_j=A(2^{j+1}\delta)$, and the run stops after the first round trip $T_J$ that visits every point, returning the walk $W=T_0T_1\cdots T_J$. Then:
--
--   1. the run stops, $W$ starts at $p$ and visits every point, and for every walk $\sigma$ from $p$ that visits every point,
--   $$
--   \mathrm{lat}(W)\;\le\;8\lceil\alpha\rceil\beta\cdot\mathrm{lat}(\sigma);
--   $$
--   2. there is one polynomial $q$, fixed before the instance and before $\alpha,\beta,A$, such that for every rational metric $d$ of bit size $s$ the number $J+1$ of calls to $A$ is at most $q(s)$.
--
--   This is the paper's Lemma 5: "A tour of latency at most $8\lceil\alpha\rceil\beta$ times the optimal can be found by making polynomially many calls to an $(\alpha,\beta)$-TSP-approximator." Together with Corollary 4 ($\alpha=3$, $\beta=6$) it gives the $144$-approximation of Theorem 6.
--
--   **Formalization Note** Total latency is measured at first visits; the comparison is with every covering walk from $p$, which is the comparison with the optimum. "Polynomially many calls" is a bound on the number of calls in terms of the bit size of a rational instance; the latency clause is stated for real distances.
--
--   Differences from the source:
--   - reading: 'calls the approximator for L = 2, 4, 8, … and then concatenates these tours to obtain a tour which visits all the vertices', with δ normalised to 1 (proof of Lemma 5, p. 6) → round trip j = 0, 1, … is A(2^{j+1}δ) with δ = nnDist d p (1 if p is the only point); the output is T_0 ++ ⋯ ++ T_J for the first J whose own tour T_J visits every point (StopsAt, doublingWalk); reason: the page leaves the stopping rule and the scale open; δ = 1 is the page's normalisation 'for simplicity of presentation', undone by scaling
--   - encoding: the optimal (p-latency: minimum total latency over all tours which start at p, p. 3; the MLT may revisit points, p. 2) → the bound holds against every walk σ from p that visits every point, latency measured at first visits; reason: comparing with every covering walk is comparing with the minimum, with no sInf over walks
--   - reading: polynomially many calls → ∃ q : Polynomial ℕ, chosen before the instance, α, β and A, with J + 1 ≤ q(instSize d) for rational distance matrices d; reason: the number of round trips depends on the ratio of the largest distance to δ, so it is polynomial in the bit size of the input, the usual meaning; the latency clause stays over ℝ
--   - generalization: α, β are the ratios of an approximator (implicitly α, β ≥ 1) → α, β arbitrary reals, no sign hypothesis; reason: specializes to α, β ≥ 1; for α ≤ 0 or β < 0 on two or more points no approximator exists, and one point has latency 0
--   - reading: an approximator given ε and L, visiting at least (1 − αε)n vertices if a tour of length L visits (1 − ε)n vertices (Definition and Comment, p. 6) → IsTSPApprox: A is called with L only and, for every k, if some rooted tour of closed length ≤ L misses ≤ k points then A L is a rooted tour of closed length ≤ βL missing ≤ αk points; reason: the Comment allows calling the approximator with L only, and Lemma 5 does so; εn = k is the number of missed points; 'a tour of length L' is read as closed length at most L
--   - reading: bounds L of the Definition (p. 6) → 0 < L; reason: L is a tour-length budget; at L = 0 the page's penalty P = 2L/(εn) is 0 and its argument ('else the penalty is more than 6L') is void; Lemma 5 calls the approximator only with L = 2^{j+1}δ > 0
--   - reading: the distances satisfy the triangle inequality / an n-point metric space (§3.2, p. 6) → IsMetric d: symmetric, zero diagonal, positive between distinct points, triangle inequality; reason: positivity is §3.2's standing assumption (metric spaces; the proof of Lemma 5 normalises the nearest-neighbour distance to 1); without it the algorithm fails: p and z_1, …, z_m at mutual distance 0 and f at distance 1 from all of them give δ = 0, and even with δ repaired to 1 a factor-2 oracle may return (p, f, z_1, …, z_m) at L = 2, with latency 1 + 2m against 1 for (p, z_1, …, z_m, f)
--   - reading: a tour starting at p (Definition and prize-collecting problem, p. 6) → IsRootedTour p T: a duplicate-free list with head p, closed by the return leg to p (tourLen); reason: a TSP tour visits each of its points once and returns to its start; the GW algorithm returns such a tour, and under the triangle inequality any closed walk from p shortcuts to one that is no longer and visits the same points, so no instance of the page changes
-- source:
--   Blum, Chalasani, Coppersmith, Pulleyblank, Raghavan, Sudan, The Minimum Latency Problem, STOC 1994 (authors' copy, sha256 7b3a41fd…3498), PDF p. 6, Lemma 5 (proof pp. 6–7)

import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

namespace MinLatency.Approx

theorem lemma_5 :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℝ) (p : V), IsMetric d →
      ∀ (α β : ℝ) (A : ℝ → List V), IsTSPApprox d p α β A →
      ∃ J : ℕ, StopsAt d p A J ∧ IsCoveringWalk p (doublingWalk d p A J) ∧
        ∀ σ : List V, IsCoveringWalk p σ →
          walkLatency d (doublingWalk d p A J) ≤
            8 * ((⌈α⌉ : ℤ) : ℝ) * β * walkLatency d σ) ∧
    (∃ q : Polynomial ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℚ) (p : V),
      IsMetric (fun u v => (d u v : ℝ)) →
      ∀ (α β : ℝ) (A : ℝ → List V), IsTSPApprox (fun u v => (d u v : ℝ)) p α β A →
      ∃ J : ℕ, StopsAt (fun u v => (d u v : ℝ)) p A J ∧ J + 1 ≤ q.eval (instSize d)) := by sorry

end MinLatency.Approx

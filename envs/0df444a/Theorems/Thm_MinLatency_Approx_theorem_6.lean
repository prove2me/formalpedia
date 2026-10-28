-- Prove2me | Theorems.Thm_MinLatency_Approx_theorem_6
-- name    : MinLatency.Approx.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:18.670978+00:00
-- url     : https://prove2.me/theorems/49d7e61a-28d6-42cd-9f00-51de37870ecc
-- title:
--   Theorem 6, p. 7 — the round-trip algorithm over any factor-2 prize-collecting TSP oracle is a 144-approximation for the MLT on metrics, with polynomially many calls
-- statement:
--   Let $d$ be a metric on a finite set $V$ of $n$ points and let $p\in V$ be the starting point. Let $O$ be any admissible prize-collecting oracle (for every nonnegative penalty vector it returns a tour rooted at $p$ of prize-collecting cost at most twice that of every tour rooted at $p$; this is the guarantee of Lemma 3). Run the algorithm of §3.2: round trip $j=0,1,2,\dots$ is the tour returned by the $(3,6)$-TSP-approximator of Corollary 4 for the budget $2^{j+1}\delta$, where $\delta$ is the distance from $p$ to its nearest neighbour, and the run stops after the first round trip that visits every point, returning the concatenation $W$ of the round trips. Then:
--
--   1. the run stops, $W$ is a walk from $p$ visiting every point, and for every walk $\sigma$ from $p$ visiting every point,
--   $$
--   \mathrm{lat}(W)\;\le\;144\cdot\mathrm{lat}(\sigma);
--   $$
--   2. there is one polynomial $q$, fixed before the instance and the oracle, such that for every rational metric of bit size $s$ the number $(J+1)\,n$ of oracle calls is at most $q(s)$, and every penalty handed to the oracle is a rational number of bit size at most $q(s)$.
--
--   This is the paper's Theorem 6, "There is a polynomial-time 144-approximation algorithm for the MLT whenever the distances $(d_{ij})$ satisfy the triangle inequality", with $144=8\lceil\alpha\rceil\beta$ for $(\alpha,\beta)=(3,6)$. It was the first constant-factor approximation for the minimum latency problem in general metrics.
--
--   **Formalization Note** "Polynomial-time" is rendered relative to the prize-collecting subroutine of Lemma 3 (Goemans–Williamson), which the paper cites without proof: the subroutine enters as an oracle with its factor-2 guarantee, and one polynomial in the bit size of a rational input bounds the number of oracle calls and the size of every penalty passed to it; everything else the algorithm does is a polynomial number of arithmetic operations on these numbers. The latency clause is stated for real distances, at full domain. The comparison with every covering walk from $p$ is the comparison with the $p$-latency, without an infimum.
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm → for every admissible oracle O, one polynomial q, chosen before the instance and O, bounds the number (J + 1)·|V| of oracle calls and the bit size of every penalty passed to O, on rational distance matrices; reason: the subroutine of Lemma 3 is cited, not proved, and needs a machine model outside the paper; the paper measures the run by the number of calls (Lemma 5: 'polynomially many calls'); no machine model
--   - reading: a 144-approximation algorithm (Lemma 5 run over Corollary 4) → the specific run doublingWalk d p (cor4Approx d p O) J, stopped at the first round trip covering every point, for every admissible oracle O; reason: the page's proof composes Lemma 5 and Corollary 4; the steps the page leaves open (δ, P = 4L at k = 0, the scan replacing binary search, the index of the budgets 2^{j+1}δ) are fixed as in the Setting definition
--   - reading: the GW algorithm of Lemma 3 ([8], cited, not proved in the paper) → an arbitrary oracle O : (V → ℝ) → List V satisfying PCAdmissible d p O; reason: Lemma 3 is cited; its guarantee enters as the property of the subroutine, and the statement holds for every such subroutine
--   - generalization: a (2 − 1/(n−1))-approximation (Lemma 3) → a factor-2 guarantee (PCAdmissible); reason: the proof of Corollary 4 uses factor 2 (p. 6: 'from a 2-approximation algorithm'); every (2 − 1/(n−1))-approximate oracle is factor-2 admissible, so the statement specializes to Lemma 3's oracle
--   - encoding: the optimal (p-latency: minimum total latency over all tours which start at p, p. 3; the MLT may revisit points, p. 2) → the bound holds against every walk σ from p that visits every point, latency measured at first visits; reason: comparing with every covering walk is comparing with the minimum, with no sInf over walks
--   - reading: the distances satisfy the triangle inequality / an n-point metric space (§3.2, p. 6) → IsMetric d: symmetric, zero diagonal, positive between distinct points, triangle inequality; reason: positivity is §3.2's standing assumption (metric spaces; the proof of Lemma 5 normalises the nearest-neighbour distance to 1); without it the algorithm fails: p and z_1, …, z_m at mutual distance 0 and f at distance 1 from all of them give δ = 0, and even with δ repaired to 1 a factor-2 oracle may return (p, f, z_1, …, z_m) at L = 2, with latency 1 + 2m against 1 for (p, z_1, …, z_m, f)
--   - reading: a tour starting at p (Definition and prize-collecting problem, p. 6) → IsRootedTour p T: a duplicate-free list with head p, closed by the return leg to p (tourLen); reason: a TSP tour visits each of its points once and returns to its start; the GW algorithm returns such a tour, and under the triangle inequality any closed walk from p shortcuts to one that is no longer and visits the same points, so no instance of the page changes
-- source:
--   Blum, Chalasani, Coppersmith, Pulleyblank, Raghavan, Sudan, The Minimum Latency Problem, STOC 1994 (authors' copy, sha256 7b3a41fd…3498), PDF p. 7, Theorem 6 (proof: 'Follows from Lemma 5 and Corollary 4.')

import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

namespace MinLatency.Approx

theorem theorem_6 :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℝ) (p : V), IsMetric d →
      ∀ O : (V → ℝ) → List V, PCAdmissible d p O →
      ∃ J : ℕ, StopsAt d p (cor4Approx d p O) J ∧
        IsCoveringWalk p (doublingWalk d p (cor4Approx d p O) J) ∧
        ∀ σ : List V, IsCoveringWalk p σ →
          walkLatency d (doublingWalk d p (cor4Approx d p O) J) ≤ 144 * walkLatency d σ) ∧
    (∃ q : Polynomial ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℚ) (p : V),
      IsMetric (fun u v => (d u v : ℝ)) →
      ∀ O : (V → ℝ) → List V, PCAdmissible (fun u v => (d u v : ℝ)) p O →
      ∃ J : ℕ, StopsAt (fun u v => (d u v : ℝ)) p (cor4Approx (fun u v => (d u v : ℝ)) p O) J ∧
        (J + 1) * Fintype.card V ≤ q.eval (instSize d) ∧
        ∀ j ≤ J, ∀ k < Fintype.card V, ∃ r : ℚ,
          (r : ℝ) = penalty (budget (fun u v => (d u v : ℝ)) p j) k ∧
          ratSize r ≤ q.eval (instSize d)) := by sorry

end MinLatency.Approx

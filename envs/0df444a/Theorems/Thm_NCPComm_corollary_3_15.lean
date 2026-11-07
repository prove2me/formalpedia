-- Prove2me | Theorems.Thm_NCPComm_corollary_3_15
-- name    : NCPComm.corollary_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:21.759371+00:00
-- url     : https://prove2.me/theorems/f4b39598-1443-4329-a202-34436159890c
-- title:
--   Corollary 3.15 — dense-input exact gap disjointness
-- statement:
--   Let $N,K,k_a,g$ be positive integers with $K=o(N)$, $k_a=o(K)$ and $1\le g\le k_a$. For all sufficiently large $N$, the public-coin communication complexity of exact $\mathrm{GapDisj}_{N,g,k_a,N-K}$, with error at most $\frac13$, is $\Omega(k_a/g)$.
--
--   Dense inputs are the case the reduction produces: Bob's vector marks the $N-K$ light elements.
--
--   Differences from the source:
--   - reading: "they must output 1 (accept)" (Definition 3.13), with "Alice's decision" on p.10 → only Alice's output must be correct; reason: stronger for a lower bound: a protocol where both are correct is one where Alice is; the page takes Alice's decision on p.10
--   - encoding: asymptotic statement in N with o(·), O(·), Ω(·) → sequences N(n), K(n), s(n) with limits and "for all large n"; reason: decision 11 of the plan; a family of parameters is what the asymptotic notation quantifies over
--   - reading: Ω(k_a/g) for all sufficiently large N → κ absolute before the sequences, threshold depending on the sequences; reason: the stronger of the two readings, and what the proof gives through Theorem 3.14
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Corollary 3.15, p.17

import Mathlib
import Definitions.Def_NCPComm_SolvesExactGapDisj

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Corollary 3.15 (Dense-input exact gap disjointness), p.17** (Herman, The Communication
Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…).
For positive integers `N, K, k_a, g` with `K = o(N)`, `k_a = o(K)` and `1 ≤ g ≤ k_a`, for all
sufficiently large `N` the public-coin communication complexity of exact
`GapDisj_{N,g,k_a,N-K}` with error at most `1/3` is `Ω(k_a/g)`.

**Formalization Note** The parameters are sequences indexed by `n`, the asymptotic hypotheses are
limits, and `κ` is absolute. `K ≥ 1` and `K/N → 0` force `N → ∞`. -/
theorem corollary_3_15 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N K ka g : ℕ → ℕ),
      (∀ᶠ n in atTop, 0 < N n ∧ 0 < K n ∧ 0 < ka n ∧ 1 ≤ g n ∧ g n ≤ ka n) →
      Tendsto (fun n => (K n : ℝ) / N n) atTop (𝓝 0) →
      Tendsto (fun n => (ka n : ℝ) / K n) atTop (𝓝 0) →
      ∀ᶠ n in atTop, ∀ (P : DistVerif.Simulation.PubProtocol (N n)) (k : ℕ),
        SolvesExactGapDisj P k (g n) (ka n) (N n - K n) (1 / 3) →
          κ * ((ka n : ℝ) / g n) ≤ (k : ℝ) := by sorry

end NCPComm

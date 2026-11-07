-- Prove2me | Theorems.Thm_MinSumClust_claim_59
-- name    : MinSumClust.claim_59
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:16.41984+00:00
-- url     : https://prove2.me/theorems/bb24e418-9aca-4ffb-beff-e3ea0f09e225
-- title:
--   Claim 59 — every outcome of Algorithms 5–7 is a partition of $D$ into exactly $k$ nonempty clusters
-- statement:
--   Let $\mathcal S_1,\mathcal S_2$ be partitions of $D$ into $k_1$ and $k_2$ clusters with $k_1\le k<k_2$. For every tie-breaking order and every outcome of the random labelings of §5.3 followed by Algorithms 5, 6 and 7, the final clusters form a partition of $D$ into exactly $k$ nonempty clusters: each final cluster is nonempty, distinct opened clusters have disjoint final clusters, every client lies in one of them, and exactly $k$ clusters are opened.
--
--   This is the feasibility half of Theorem 3.
--
--   Differences from the source:
--
--   - reading: the final clusters of the algorithm → the final clusters of every outcome in the support of Algorithms 5–7, for every tie ranking; reason: the claim holds surely, not only in expectation
--   - generalization: §5 assumes α ≤ 1/2 w.l.o.g. (p.42) → no assumption on α; reason: the proof (Claims 58–59) does not use it; the paper's case is included
--   - encoding: the final clusters → final clusters indexed by the opened clusters tagged with their side (𝒮₁ or 𝒮₂); "exactly k" counts the opened clusters; reason: a set can be a cluster of both solutions; Claim 58 counts opened clusters
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Claim 59, p.57 (PDF p.59); Claim 58, p.56

import Mathlib
import Definitions.Def_MinSumClust_alg7
import Definitions.Def_MinSumClust_round

namespace MinSumClust

/-- **Claim 59**, p.57 (PDF p.59).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Claim 59, p.57.

Let `𝒮₁, 𝒮₂` be partitions of `D` into `k₁` and `k₂` clusters with `k₁ ≤ k < k₂`. Every outcome of
Algorithms 5–7 (with the labelings of §5.3) is a partition of `D` into exactly `k` nonempty clusters.

**Formalization Note.** "Every outcome" is every point of the support of `alg567`, for every tie
ranking `rk`. The final clusters are indexed by the opened clusters tagged with their side, so
"exactly k" counts the opened clusters (Claim 58). The section's standing "w.l.o.g. α ≤ 1/2" (p.42)
is not assumed; the claim's proof does not use it. -/
theorem claim_59 {D : Type} [Fintype D] [DecidableEq D]
    (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (k : ℕ) (hk₁ : S₁.parts.card ≤ k)
    (hk₂ : k < S₂.parts.card) (rk : Finset D → ℕ) :
    ∀ o ∈ (alg567 S₁ S₂ k rk).support, IsKOutcome o k := by sorry

end MinSumClust

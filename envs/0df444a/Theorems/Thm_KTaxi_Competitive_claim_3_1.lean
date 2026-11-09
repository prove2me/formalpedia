-- Prove2me | Theorems.Thm_KTaxi_Competitive_claim_3_1
-- name    : KTaxi.Competitive.claim_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:29:12.01142+00:00
-- url     : https://prove2.me/theorems/78336425-06be-4848-ae95-489fb751ad04
-- title:
--   Claim 3.1 — effect at each level: the new level-$m$ prefix is $X_m-x_{j_m}+r$
-- statement:
--   Let $x=(x_1,\dots,x_k)$ be the ordered list, $r$ the pickup and $\zeta_1,\dots,\zeta_k$ any real clock values attached to the positions. For $1\le m\le k$ let $j_m=\arg\min_{1\le i\le m}\zeta_i$ be the local winner of the original level-$m$ prefix, ties broken by the smallest index, and let $X_m$ be the multiset of locations in that prefix. After Algorithm 1 updates the list (the scan with these clocks) and moves the first taxi to $r$, the multiset of locations in the new level-$m$ prefix is
--   $$
--   X_m-x_{j_m}+r .
--   $$
--   So each prefix evolves as if its local winner had been moved to $r$, which lets the analysis treat each level separately.
--
--   **Formalization Note** The claim is deterministic, for every vector of clock values. The local winner $j$ is given by its defining properties: $j<m$, $\zeta_j\le\zeta_i$ for all $i<m$, and $\zeta_j<\zeta_i$ for all $i<j$. $X-x+r$ is `r ::ₘ X.erase x`.
--
--   Differences from the source:
--   - encoding: 1-based ranks i = 1, …, k → 0-based slots j : Fin k (rank j + 1); levels m : ℕ count leading slots; reason: Lean convention; same instances
--   - encoding: j_m = arg min_{1≤i≤m} ζ_i with ties broken by the smallest index → any j < m with ζ_j ≤ ζ_i for i < m and ζ_j < ζ_i for i < j; reason: this characterises the tie-broken argmin uniquely
--   - generalization: k ≥ 2 (standing assumption, PDF p. 4) → k ≥ 1, including the one-taxi case; reason: the statement also holds for one taxi and specializes to every k ≥ 2; at k = 1 the scan is the identity, the matching has one edge, and any lower-level sum is empty
--   - generalization: clock values sampled by Algorithm 1 (nonnegative almost surely) → every real clock vector ζ; reason: the prefix identity depends only on comparisons in the deterministic scan; it specializes to the sampled clock vectors
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Claim 3.1, PDF p. 5 (printed p. 4)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Analysis

namespace KTaxi.Competitive

open Classical in
/-- **Claim 3.1** (effect at each level; PDF p. 5). Let `x` be the ordered list, `r` the pickup
and `ζ` any clock values (indexed by the original slots). Let `1 ≤ m ≤ k` and let `j` be the
local winner of the original level-`m` prefix: `ζ_j = min_{i < m} ζ_i`, ties broken by the
smallest index. After the list update of Algorithm 1 and the movement of the first taxi to `r`,
the multiset of locations in the new level-`m` prefix is `X_m - x_j + r`. -/
theorem claim_3_1 {V : Type*} [MetricSpace V] {k : ℕ} [NeZero k] (x : Fin k → V) (r : V)
    (ζ : Fin k → ℝ) (m : ℕ) (hm : m ≤ k) (j : Fin k) (hjm : j.val < m)
    (hmin : ∀ i : Fin k, i.val < m → ζ j ≤ ζ i) (hfirst : ∀ i : Fin k, i < j → ζ j < ζ i) :
    prefixMultiset (afterRound x (scanPerm ζ) r) m = r ::ₘ (prefixMultiset x m).erase (x j) := by sorry

end KTaxi.Competitive

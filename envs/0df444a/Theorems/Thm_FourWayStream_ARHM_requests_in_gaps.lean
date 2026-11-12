-- Prove2me | Theorems.Thm_FourWayStream_ARHM_requests_in_gaps
-- name    : FourWayStream.ARHM.requests_in_gaps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:43:57.933213+00:00
-- url     : https://prove2.me/theorems/1e343c91-e626-4c53-a8ab-7eacfd5bdcd2
-- title:
--   Lemma 5.5 — requests in a set of gaps: $P[Y\ge k]\le\binom mk\frac{(\mu N)^{\bar k}}{(NL+1)^{\bar k}}\le(e/(50k))^k$
-- statement:
--   **Lemma 5.5 (Requests in a set of gaps).** Let $N$ be even, $2\le m\le\lfloor\sqrt N\rfloor$, $\mu=100m$ and $L=\mu^2$. In a uniformly random order of the stream, gap $j$ ($0\le j\le NL$) holds the requests that arrive after exactly $j$ updates. Let $Y$ be the number of requests in a fixed set $J$ of at most $\mu N$ gaps; the gaps in $J$ need not be consecutive. For $1\le k\le m$,
--   $$P[Y\ge k]\le\binom mk\frac{(\mu N)^{\bar k}}{(NL+1)^{\bar k}}\le\Big(\frac{e}{50k}\Big)^k,$$
--   where $a^{\bar k}=a(a+1)\cdots(a+k-1)$ is the rising factorial.
--
--   It bounds how many requests a single bank must serve, which drives the exhaustion estimate of Lemma 5.6.
--
--   Differences from the source:
--   - encoding: a uniform interleaving of the NL update symbols with the m request symbols (a uniform weak composition of m into NL + 1 parts) → gaps computed from a uniformly random bijection Fin (N·L + m) ≃ (Fin N × Fin L) ⊕ Fin m; reason: the interleaving induced by the uniform random order is uniform (§5.1.1); Y is the same random variable
--   - encoding: a set J of at most µN gaps → J ⊆ {0, …, NL} as a Finset ℕ with |J| ≤ 100·m·N; reason: gaps are the numbers 0, …, NL
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.1.1, p.21, Lemma 5.5

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Rebuild

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Lemma 5.5 (Requests in a set of gaps), p.21. Let `N` be even, `2 ≤ m ≤ ⌊√N⌋`, `µ = 100m`,
`L = µ²`, and let `Y` be the number of requests in a fixed set `J` of at most `µN` gaps (not
necessarily consecutive) under the uniformly random arrival order. For `1 ≤ k ≤ m`,
`P[Y ≥ k] ≤ C(m,k) (µN)^{k̄} / (NL + 1)^{k̄} ≤ (e/(50k))^k`. -/
theorem requests_in_gaps (N m : ℕ) (hN : Even N) (hm : 2 ≤ m) (hmN : m ≤ Nat.sqrt N)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range (N * (100 * m) ^ 2 + 1)) (hJc : J.card ≤ 100 * m * N)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    ((Finset.univ.filter (fun σ : Arrival N m ((100 * m) ^ 2) => k ≤ requestsIn σ J)).card : ℝ) /
        (Fintype.card (Arrival N m ((100 * m) ^ 2)) : ℝ) ≤
      (m.choose k : ℝ) * risingFact ((100 * m * N : ℕ) : ℝ) k /
        risingFact ((N * (100 * m) ^ 2 + 1 : ℕ) : ℝ) k ∧
    (m.choose k : ℝ) * risingFact ((100 * m * N : ℕ) : ℝ) k /
        risingFact ((N * (100 * m) ^ 2 + 1 : ℕ) : ℝ) k ≤ (Real.exp 1 / (50 * k)) ^ k := by sorry

end FourWayStream.ARHM

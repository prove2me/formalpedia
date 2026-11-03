-- Prove2me | Theorems.Thm_FreeOrderEPTAS_bucket_facts
-- name    : FreeOrderEPTAS.bucket_facts
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:10.199215+00:00
-- url     : https://prove2.me/theorems/aba2441c-5e29-4d5a-b3d7-90c7d63027b3
-- title:
--   §3.2 — $K\le1/\epsilon$ and the stable buckets (corrected: half-open jumps, Figure 1 indexing)
-- statement:
--   Let $\sigma$ be a permutation with $V^*_t=R_t$ and $1/\epsilon$ a positive integer. For the corrected buckets:
--
--   1. $K\le1/\epsilon$;
--   2. every stable bucket has $\mathrm{BaseVal}(B_{i+1})-\mathrm{BaseVal}(B_i)\le\epsilon V^*_1$, strictly if $V^*_1>0$;
--   3. every jump bucket holds exactly one variable;
--   4. every variable lies in one of the $2K+1$ buckets;
--   5. on a nonempty bucket, $\mathrm{BaseVal}(B_i)=V^*_{\max\{t:X_{\sigma(t)}\in B_i\}+1}$;
--   6. $\mathrm{BaseVal}(B_1)=0$, and at the index above the top bucket $\mathrm{BaseVal}=V^*_1$.
--
--   These are the facts about the partition that Claims 3.4 and 3.5 use.
--
--   Differences from the source:
--   - correction: jump iff the closed interval $[V^*_t,V^*_{t-1}]$ contains a multiple of $\epsilon V^*_1$; $B_2=\{X_{\sigma^*(T_K)}\}$, p.17 → jump variable at $s$ iff $(V^*_{s+1},V^*_s]$ contains a multiple; buckets as in Figure 1; reason: $\epsilon=1/2$, values $(1,0,0,0,0)$, $\sigma^*$ the identity: closed intervals give $K\ge4>1/\epsilon$; values $(1,0.6,0.6,0)$: the text’s stable bucket has step $0.6>\epsilon\mathrm{OPT}$, against Figure 1 and the proof of Claim 3.4
--   - generalization: an optimal permutation $\sigma^*$ → every permutation $\sigma$; reason: no step uses optimality; $\sigma^*$ is a permutation
--   - reading: $\mathrm{BaseVal}(B_{2K+2})$, undefined → $V^*_1$ at the index above the top bucket; reason: the value (15) needs at the top bucket; $\mathrm{OPT}$ for optimal $\sigma$
--   - encoding: times and buckets $1,\dots,n$ and $1,\dots,2K+1$ → 0-based `Fin n`, `Fin (2K+1)`; even index stable, odd index jump; reason: a shift of indices; same objects
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.2, pp.17–18, Figure 1

import Mathlib
import Definitions.Def_FreeOrderEPTAS_bucket

namespace FreeOrderEPTAS

/-- §3.2, pp.17–18 (arXiv:2007.13121v3), for the corrected buckets of any permutation `σ` with
`1/ϵ ∈ ℕ`, where `V*_s = R I σ s` (0-based) and `K = numJumps`:
1. `K ≤ 1/ϵ`;
2. every stable (even) bucket has `BaseVal(B_{i+1}) - BaseVal(B_i) ≤ ϵ V*_0`, strictly when `V*_0 > 0`;
3. every jump (odd) bucket consists of exactly one variable;
4. the buckets are `0, …, 2K`;
5. `BaseVal(B_i) = V*_{max{t : X_{σ(t)} ∈ B_i}+1}` on a nonempty bucket;
6. `BaseVal(B_1) = 0`, and at the index `2K + 1` above the top bucket `BaseVal = V*_0`. -/
theorem bucket_facts {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ : ℝ) (q : ℕ) (hq : 0 < q)
    (hϵ : ϵ = 1 / (q : ℝ)) :
    (numJumps I σ ϵ : ℝ) ≤ 1 / ϵ ∧
    (∀ i, i < 2 * numJumps I σ ϵ + 1 → Even i →
      BaseVal I σ ϵ (i + 1) - BaseVal I σ ϵ i ≤ ϵ * R I σ 0 ∧
        (0 < R I σ 0 → BaseVal I σ ϵ (i + 1) - BaseVal I σ ϵ i < ϵ * R I σ 0)) ∧
    (∀ i, i < 2 * numJumps I σ ϵ + 1 → Odd i → ∃! s, s < n ∧ bucket I σ ϵ s = i) ∧
    (∀ s, s < n → bucket I σ ϵ s < 2 * numJumps I σ ϵ + 1) ∧
    (∀ s, s < n → (∀ s', s' < n → bucket I σ ϵ s' = bucket I σ ϵ s → s' ≤ s) →
      BaseVal I σ ϵ (bucket I σ ϵ s) = R I σ (s + 1)) ∧
    BaseVal I σ ϵ 0 = 0 ∧
    BaseVal I σ ϵ (2 * numJumps I σ ϵ + 1) = R I σ 0 := by sorry

end FreeOrderEPTAS

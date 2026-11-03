-- Prove2me | Theorems.Thm_FreeOrderEPTAS_claim_3_5
-- name    : FreeOrderEPTAS.claim_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:17.314316+00:00
-- url     : https://prove2.me/theorems/9cd91836-00e5-4453-8039-3fd2956d945f
-- title:
--   Claim 3.5 — the value before $t_{\min}$ (corrected: buckets)
-- statement:
--   Under the situation of §3.5, with $t_{\min}$ and $B$ as in Claim 3.4,
--   $$\sum_{t<t_{\min}}(R_t-R_{t+1})\ge(1-\epsilon)\sum_{i>B}\big(\mathrm{BaseVal}(B_{i+1})-\mathrm{BaseVal}(B_i)\big)-3\epsilon\cdot\mathrm{OPT}.$$
--   If no time is ahead of schedule, the same bound holds with $t_{\min}=n+1$ and the sum over all buckets.
--
--   The constant $3$ comes from $2K+1\le3/\epsilon$ in (19).
--
--   Differences from the source:
--   - correction: jump iff the closed interval $[V^*_t,V^*_{t-1}]$ contains a multiple of $\epsilon V^*_1$; $B_2=\{X_{\sigma^*(T_K)}\}$, p.17 → jump variable at $s$ iff $(V^*_{s+1},V^*_s]$ contains a multiple; buckets as in Figure 1; reason: $\epsilon=1/2$, values $(1,0,0,0,0)$, $\sigma^*$ the identity: closed intervals give $K\ge4>1/\epsilon$; values $(1,0.6,0.6,0)$: the text’s stable bucket has step $0.6>\epsilon\mathrm{OPT}$, against Figure 1 and the proof of Claim 3.4
--   - reading: $t_{\min}$ always exists → a second part for the case that no time is ahead, with $t_{\min}=n+1$; reason: machine 1 may be empty
--   - encoding: times and buckets $1,\dots,n$ and $1,\dots,2K+1$ → 0-based `Fin n`, `Fin (2K+1)`; even index stable, odd index jump; reason: a shift of indices; same objects
--   - reading: $\mathrm{BaseVal}(B_{2K+2})$, needed in (15) for the top bucket, undefined → $V^*_1$ (`BaseVal` at the index $2K+1$); reason: the value (15) needs at the top bucket; it is $\mathrm{OPT}$ for optimal $\sigma^*$
--   - encoding: the guesses are read from the enumerated grid → non-negativity is a clause of `IsGuess`; reason: the grid is non-negative; p.20 uses "the non-negativity of BaseGuess"
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Claim 3.5, p.21; (18), (19), p.22

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Schedule
import Definitions.Def_FreeOrderEPTAS_orderOf

namespace FreeOrderEPTAS

/-- Claim 3.5, p.21 (arXiv:2007.13121v3):
`∑_{t < t_min} (R_t - R_{t+1}) ≥ (1 - ϵ) ∑_{i > B} (BaseVal(B_{i+1}) - BaseVal(B_i)) - 3ϵ OPT`, for
the bucket `B` of `X_{σ(t_min)}`. Second part: if no time is ahead of schedule, the same bound with
`t_min = n + 1` and the sum over all buckets. -/
theorem claim_3_5 {n : ℕ} (I : Instance n) (σs : Equiv.Perm (Fin n)) (ϵ E : ℝ)
    (b Δ : Fin (2 * numJumps I σs ϵ + 1) → ℝ) (x : Assignment (2 * numJumps I σs ϵ + 1) n)
    (h : Schedule I σs ϵ E b Δ x) :
    (∀ (t : Fin n) (i₀ : Fin (2 * numJumps I σs ϵ + 1)), IsFirstAhead I (orderOf x) b x t i₀ →
      (1 - ϵ) * ∑ i with i₀ < i, (BaseVal I σs ϵ (i.val + 1) - BaseVal I σs ϵ i.val) -
          3 * ϵ * OPT I ≤
        ∑ t' ∈ Finset.range t.val, (R I (orderOf x) t' - R I (orderOf x) (t' + 1))) ∧
    ((∀ (t : Fin n) (i : Fin (2 * numJumps I σs ϵ + 1)), x i (orderOf x t) = true →
        R I (orderOf x) (t.val + 1) < b i) →
      (1 - ϵ) * ∑ i : Fin (2 * numJumps I σs ϵ + 1),
          (BaseVal I σs ϵ (i.val + 1) - BaseVal I σs ϵ i.val) - 3 * ϵ * OPT I ≤
        ∑ t' ∈ Finset.range n, (R I (orderOf x) t' - R I (orderOf x) (t' + 1))) := by sorry

end FreeOrderEPTAS

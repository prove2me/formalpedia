-- Prove2me | Theorems.Thm_FreeOrderEPTAS_claim_3_4
-- name    : FreeOrderEPTAS.claim_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:23.045817+00:00
-- url     : https://prove2.me/theorems/fecc57ef-5639-4ac3-9f04-64b7a4ebe728
-- title:
--   Claim 3.4 — the value at $t_{\min}$ (corrected: buckets)
-- statement:
--   Under the situation of §3.5, let $t_{\min}$ be the minimal time when $\sigma$ is ahead of schedule, with $X_{\sigma(t_{\min})}$ on the machine of bucket $B$. Then
--   $$R_{t_{\min}}\ge\mathrm{BaseVal}(B)+(1-\epsilon)\,\mathrm{DeltaGuess}(B)-2\epsilon\cdot\mathrm{OPT}.$$
--
--   The stable case uses $\mathrm{DeltaGuess}(B)\le\epsilon\,\mathrm{OPT}$, which needs the corrected buckets.
--
--   Differences from the source:
--   - correction: jump iff the closed interval $[V^*_t,V^*_{t-1}]$ contains a multiple of $\epsilon V^*_1$; $B_2=\{X_{\sigma^*(T_K)}\}$, p.17 → jump variable at $s$ iff $(V^*_{s+1},V^*_s]$ contains a multiple; buckets as in Figure 1; reason: $\epsilon=1/2$, values $(1,0,0,0,0)$, $\sigma^*$ the identity: closed intervals give $K\ge4>1/\epsilon$; values $(1,0.6,0.6,0)$: the text’s stable bucket has step $0.6>\epsilon\mathrm{OPT}$, against Figure 1 and the proof of Claim 3.4
--   - reading: "This index is well-defined, since we are always ahead of schedule at time $n$" → $t_{\min}$ exists and $X_{\sigma(t_{\min})}$ is assigned, as hypotheses; reason: the printed reason assumes that $\sigma(n)$ sits on machine 1, which may hold nothing; the other case is the second part of `claim_3_5`
--   - encoding: times and buckets $1,\dots,n$ and $1,\dots,2K+1$ → 0-based `Fin n`, `Fin (2K+1)`; even index stable, odd index jump; reason: a shift of indices; same objects
--   - reading: $\mathrm{BaseVal}(B_{2K+2})$, needed in (15) for the top bucket, undefined → $V^*_1$ (`BaseVal` at the index $2K+1$); reason: the value (15) needs at the top bucket; it is $\mathrm{OPT}$ for optimal $\sigma^*$
--   - encoding: the guesses are read from the enumerated grid → non-negativity is a clause of `IsGuess`; reason: the grid is non-negative; p.20 uses "the non-negativity of BaseGuess"
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Claim 3.4, p.21

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Schedule
import Definitions.Def_FreeOrderEPTAS_orderOf

namespace FreeOrderEPTAS

/-- Claim 3.4, p.21 (arXiv:2007.13121v3):
`R_{t_min} ≥ BaseVal(B) + (1 - ϵ) DeltaGuess(B) - 2ϵ OPT`, for the bucket `B` of `X_{σ(t_min)}`. -/
theorem claim_3_4 {n : ℕ} (I : Instance n) (σs : Equiv.Perm (Fin n)) (ϵ E : ℝ)
    (b Δ : Fin (2 * numJumps I σs ϵ + 1) → ℝ) (x : Assignment (2 * numJumps I σs ϵ + 1) n)
    (h : Schedule I σs ϵ E b Δ x) (t : Fin n) (i : Fin (2 * numJumps I σs ϵ + 1))
    (ht : IsFirstAhead I (orderOf x) b x t i) :
    BaseVal I σs ϵ i.val + (1 - ϵ) * Δ i - 2 * ϵ * OPT I ≤ R I (orderOf x) t.val := by sorry

end FreeOrderEPTAS

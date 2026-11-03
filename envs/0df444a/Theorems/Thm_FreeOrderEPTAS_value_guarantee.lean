-- Prove2me | Theorems.Thm_FreeOrderEPTAS_value_guarantee
-- name    : FreeOrderEPTAS.value_guarantee
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:42.898403+00:00
-- url     : https://prove2.me/theorems/f81cfcce-b21c-41e4-bc49-d09a78eddcbb
-- title:
--   §3.5 — $V(\sigma)\ge(1-7\epsilon)\mathrm{OPT}$ (corrected: buckets)
-- statement:
--   Under the situation of §3.5, the permutation $\sigma$ built from the assignment $x$ satisfies
--   $$V(\sigma)\ge(1-7\epsilon)\cdot\mathrm{OPT}.$$
--
--   It combines Claims 3.4 and 3.5 with $V(\sigma)=R_1=R_{t_{\min}}+\sum_{t<t_{\min}}(R_t-R_{t+1})$, or with Claim 3.5 alone if no time is ahead of schedule.
--
--   Differences from the source:
--   - correction: jump iff the closed interval $[V^*_t,V^*_{t-1}]$ contains a multiple of $\epsilon V^*_1$; $B_2=\{X_{\sigma^*(T_K)}\}$, p.17 → jump variable at $s$ iff $(V^*_{s+1},V^*_s]$ contains a multiple; buckets as in Figure 1; reason: $\epsilon=1/2$, values $(1,0,0,0,0)$, $\sigma^*$ the identity: closed intervals give $K\ge4>1/\epsilon$; values $(1,0.6,0.6,0)$: the text’s stable bucket has step $0.6>\epsilon\mathrm{OPT}$, against Figure 1 and the proof of Claim 3.4
--   - reading: the permutation orders the assigned variables only → unassigned variables come after all assigned ones; reason: §3.5 is silent; a total permutation is needed
--   - encoding: times and buckets $1,\dots,n$ and $1,\dots,2K+1$ → 0-based `Fin n`, `Fin (2K+1)`; even index stable, odd index jump; reason: a shift of indices; same objects
--   - reading: $\mathrm{BaseVal}(B_{2K+2})$, needed in (15) for the top bucket, undefined → $V^*_1$ (`BaseVal` at the index $2K+1$); reason: the value (15) needs at the top bucket; it is $\mathrm{OPT}$ for optimal $\sigma^*$
--   - encoding: the guesses are read from the enumerated grid → non-negativity is a clause of `IsGuess`; reason: the grid is non-negative; p.20 uses "the non-negativity of BaseGuess"
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.5, pp.20, 22; (16), p.21

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Schedule
import Definitions.Def_FreeOrderEPTAS_orderOf

namespace FreeOrderEPTAS

/-- §3.5, pp.20, 22 (arXiv:2007.13121v3): the permutation built from the assignment of Corollary 3.3
has `V(σ) ≥ (1 - 7ϵ) OPT`. -/
theorem value_guarantee {n : ℕ} (I : Instance n) (σs : Equiv.Perm (Fin n)) (ϵ E : ℝ)
    (b Δ : Fin (2 * numJumps I σs ϵ + 1) → ℝ) (x : Assignment (2 * numJumps I σs ϵ + 1) n)
    (h : Schedule I σs ϵ E b Δ x) :
    (1 - 7 * ϵ) * OPT I ≤ V I (orderOf x) := by sorry

end FreeOrderEPTAS

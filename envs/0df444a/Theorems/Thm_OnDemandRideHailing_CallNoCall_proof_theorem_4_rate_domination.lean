-- Prove2me | Theorems.Thm_OnDemandRideHailing_CallNoCall_proof_theorem_4_rate_domination
-- name    : OnDemandRideHailing.CallNoCall.proof_theorem_4_rate_domination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:59:58.796334+00:00
-- url     : https://prove2.me/theorems/9d96bcac-e88b-40d2-82c9-575e13eda721
-- title:
--   Proof of Theorem 4: the no-call service rate is at least the one-direction call service rate in every state (corrected: $\le$ in general, $<$ except at $\lambda=0,\ n>k$ and at $n=k=1$)
-- statement:
--   A circular road of perimeter $R>0$ carries $k\ge1$ taxis moving at constant speed $v>0$; passengers arrive as a Poisson process of rate $\lambda\ge0$ at uniformly distributed locations and request rides whose length is exponential with mean $d>0$ (§3, pp. 7–8). Let $\mu^{(1c)}_n$ be the call service rates (1) and $\mu^{(nc)}_n$ the no-call service rates (3). Then
--
--   1. $\mu^{(1c)}_n\le\mu^{(nc)}_n$ for every state $n\ge1$;
--   2. $\mu^{(1c)}_n<\mu^{(nc)}_n$ for every state $n\ge1$, except when $\lambda=0$ and $n>k$, or $n=k=1$ (where the two rates coincide).
--
--   In words, the approximated no-call system serves at least as fast as the approximated one-direction call system in every state, and strictly faster in every state except the two corners where the exponential factor of (3) is identically $1$. This is the first step of the proof of Theorem 4.
--
--   Differences from the source:
--
--   - correction: µ(nc)_n > µ(1c)_n for all n → µ(1c)_n ≤ µ(nc)_n for every n ≥ 1, and µ(1c)_n < µ(nc)_n for every n ≥ 1 except when λ = 0 and n > k, or n = k = 1; reason: the printed strict claim is false at (a) λ = 0, n = k + 1 (both rates equal k/(d/v + R/(2v)); e.g. d = 2, v = 1, k = 3, R = 10 gives 0.428571… for both) and at (b) k = n = 1, any λ (the factor n − 1 = 0, both rates 1/(d/v + R/(2v))); both corners satisfy every assumption of the paper, and they are exactly the states where the rates coincide, so the strict claim is kept at every other state
--   - reading: §3's model (pp. 7–8): λ a Poisson arrival rate, d the mean of an exponential ride distance, v a speed, R the perimeter of the road, k the number of taxis; Theorem 4 says 'for any λ, d, v, k and R' → hypotheses 0 ≤ lam, 0 < d, 0 < v, 0 < R, 1 ≤ k; reason: the model states these once; they exclude only parameter values that are not the model (negative rates, empty road, no taxis), and at k = 0 every rate of (1) and (3) is 0. λ ≥ kv/d is not excluded
--   - encoding: for all n → for every n ≥ 1; reason: the queue uses only µ1, µ2, …; at n = 0 both rates are 0
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, proof of Theorem 4, unnumbered step, p. 38

import Mathlib
import Definitions.Def_OnDemandRideHailing_CallNoCall_muCall1
import Definitions.Def_OnDemandRideHailing_CallNoCall_muNoCall

namespace OnDemandRideHailing.CallNoCall

/-- **Proof of Theorem 4: the no-call service rate is at least the one-direction call service
rate in every state (corrected: `≤` in general, `<` except at `λ = 0, n > k` and at `n = k = 1`).**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, proof of Theorem 4, p. 38: "It is easy to see that `µ(nc)_n > µ(1c)_n` for all
`n` (because `µ(1c)_n` is just `µ(nc)_n` without the exponential part in the denominator)."

Under the standing assumptions of §3 (pp. 7–8: `λ ≥ 0`, `d, v, R > 0`, `k ≥ 1`):
1. `µ(1c)_n ≤ µ(nc)_n` for every state `n ≥ 1`;
2. `µ(1c)_n < µ(nc)_n` for every state `n ≥ 1`, except when `λ = 0` and `n > k`, or `n = k = 1`.

**Formalization Note (correction).** The printed strict inequality for all `n` is false at two
corners that satisfy every assumption of the paper: (a) `λ = 0`, `n = k + 1`, where both rates
equal `k/(d/v + R/(2v))` (`∫_0^{R/v} (R−vt)/R dt = R/(2v)` and `exp 0 = 1`); (b) `k = n = 1`, any
`λ`, where the factor `n − 1 = 0` kills the exponential and both rates equal
`1/(d/v + R/(2v))`. The corrected statement keeps the non-strict inequality everywhere (which is
all Theorem 4 needs) and the strict one at every other state: these two corners are exactly the
states where the rates coincide (for `n < k` the exponential-free integral is already
`R/(v(k−n+2)) < R/(v(k−n+1))`; for `n = k ≥ 2`, and for `n > k` with `λ > 0`, the exponential is
`< 1` on `(0, R/v]`). -/
theorem proof_theorem_4_rate_domination {lam d v R : ℝ} {k : ℕ}
    (hlam : 0 ≤ lam) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k) :
    (∀ n : ℕ, 1 ≤ n → muCall1 d v k R n ≤ muNoCall lam d v k R n) ∧
      (∀ n : ℕ, 1 ≤ n → ¬ (lam = 0 ∧ k < n) → ¬ (n = 1 ∧ k = 1) →
        muCall1 d v k R n < muNoCall lam d v k R n) := by sorry

end OnDemandRideHailing.CallNoCall

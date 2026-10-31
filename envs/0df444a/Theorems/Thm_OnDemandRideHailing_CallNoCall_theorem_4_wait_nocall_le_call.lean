-- Prove2me | Theorems.Thm_OnDemandRideHailing_CallNoCall_theorem_4_wait_nocall_le_call
-- name    : OnDemandRideHailing.CallNoCall.theorem_4_wait_nocall_le_call
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-30T03:02:11.92427+00:00
-- url     : https://prove2.me/theorems/6efe3778-c963-43c9-8645-6041a9cfc93e
-- title:
--   Theorem 4: in the approximation scheme, the no-call average waiting time is at most the one-direction call average waiting time
-- statement:
--   A circular road of perimeter $R>0$ carries $k\ge1$ taxis moving at constant speed $v>0$; passengers arrive as a Poisson process of rate $\lambda\ge0$ at uniformly distributed locations and request rides whose length is exponential with mean $d>0$ (§3, pp. 7–8). Let $\mathcal W^{(nc)}(\lambda,d,v,k,R)$ and $\mathcal W^{(1c)}(\lambda,d,v,k,R)$ be the average waiting times of the approximated no-call system (rates (3)) and of the approximated one-direction call system (rates (1)), each equal to $+\infty$ when its queue is unstable. Then
--
--   $$
--   \mathcal W^{(nc)}(\lambda,d,v,k,R)\le\mathcal W^{(1c)}(\lambda,d,v,k,R)
--   $$
--
--   for every $\lambda\ge0$, $d,v,R>0$ and $k\ge1$, including $\lambda\ge kv/d$, where the right side is $+\infty$.
--
--   Within the paper's queueing approximation, street-hailing never makes passengers wait longer on average than one-direction platform matching: matching the nearest pair at once forgoes the more efficient pairings that arise when a taxi simply picks up the first passenger it passes.
--
--   Differences from the source:
--
--   - reading: §3's model (pp. 7–8): λ a Poisson arrival rate, d the mean of an exponential ride distance, v a speed, R the perimeter of the road, k the number of taxis; Theorem 4 says 'for any λ, d, v, k and R' → hypotheses 0 ≤ lam, 0 < d, 0 < v, 0 < R, 1 ≤ k; reason: the model states these once; they exclude only parameter values that are not the model (negative rates, empty road, no taxis), and at k = 0 every rate of (1) and (3) is 0. λ ≥ kv/d is not excluded
--   - encoding: the average waiting time W of the approximating M/M/k queue, given on p. 34 by Σ_{i≥1} iλ^{i−1}/(µ1⋯µi) / (1 + Σ_{i≥1} λ^i/(µ1⋯µi)) − d/v, with W = ∞ when the queue is not stable → avgWait: the same formula (numerator reindexed i ↦ i+1) as an EReal when both series are summable, ⊤ otherwise; reason: the paper takes the formula from standard queueing theory and uses exactly this ∞ convention (p. 34); no CTMC or Little's law is formalized
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, §6, Theorem 4, p. 21; proof pp. 38–39

import Mathlib
import Definitions.Def_OnDemandRideHailing_CallNoCall_QueueStable
import Definitions.Def_OnDemandRideHailing_CallNoCall_waitFormula
import Definitions.Def_OnDemandRideHailing_CallNoCall_avgWait
import Definitions.Def_OnDemandRideHailing_CallNoCall_muCall1
import Definitions.Def_OnDemandRideHailing_CallNoCall_muNoCall
import Definitions.Def_OnDemandRideHailing_CallNoCall_W1c
import Definitions.Def_OnDemandRideHailing_CallNoCall_Wnc

namespace OnDemandRideHailing.CallNoCall

/-- **Theorem 4: in the approximation scheme, the no-call average waiting time is at most the
one-direction call average waiting time.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, §6, Theorem 4, p. 21: "For any `λ, d, v, k` and `R`,
`W(nc)(λ, d, v, k, R) ≤ W(1c)(λ, d, v, k, R)`", "using the approximation scheme introduced in
Section 5" (p. 21). Proof on pp. 38–39.

For every arrival rate `λ ≥ 0`, mean ride distance `d > 0`, speed `v > 0`, road perimeter
`R > 0` and number of taxis `k ≥ 1` (§3, pp. 7–8), the average waiting time of the approximated
no-call system (service rates (3)) is at most that of the approximated one-direction call system
(service rates (1)).

**Formalization Note.** Both waiting times are the p. 34 formula in `EReal`, `+∞` when the
queue is unstable. "For any `λ`" includes `λ ≥ kv/d`, where `W^(1c) = +∞` (Theorem 1(1)). -/
theorem theorem_4_wait_nocall_le_call {lam d v R : ℝ} {k : ℕ}
    (hlam : 0 ≤ lam) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k) :
    Wnc lam d v k R ≤ W1c lam d v k R := by sorry

end OnDemandRideHailing.CallNoCall

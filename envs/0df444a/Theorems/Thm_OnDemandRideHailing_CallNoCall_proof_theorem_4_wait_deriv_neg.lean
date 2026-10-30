-- Prove2me | Theorems.Thm_OnDemandRideHailing_CallNoCall_proof_theorem_4_wait_deriv_neg
-- name    : OnDemandRideHailing.CallNoCall.proof_theorem_4_wait_deriv_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:00:41.30873+00:00
-- url     : https://prove2.me/theorems/b2f5eb82-1d27-436a-b08a-23ca6f47a8e3
-- title:
--   Proof of Theorem 4: in a state-dependent M/M/k queue, $\partial\mathcal W/\partial\mu_m<0$ for every $m$
-- statement:
--   Consider a state-dependent M/M/k queue with arrival rate $\lambda>0$ and service rates $\mu_i>0$ ($i\ge1$) such that both series of the waiting-time formula converge. For a constant $s$ let
--
--   $$
--   \mathcal W=\frac{\sum_{i\ge1} i\lambda^{i-1}/(\mu_1\cdots\mu_i)}{1+\sum_{i\ge1}\lambda^{i}/(\mu_1\cdots\mu_i)}-s .
--   $$
--
--   Then for every state $m\ge1$, $\mathcal W$ viewed as a function of $\mu_m$ alone (all other rates fixed) is differentiable at the current value of $\mu_m$, and
--
--   $$
--   \frac{\partial\mathcal W}{\partial\mu_m}<0 .
--   $$
--
--   Raising the service rate of a single state shortens the average waiting time. This is the key computation of the proof of Theorem 4.
--
--   Differences from the source:
--
--   - reading: '∂W/∂µm < 0 for any m and µm' in a state-dependent M/M/k queue, with the proof's W = (1/λ)(…) → hypotheses 0 < lam, ∀ i ≥ 1, 0 < μ i, 1 ≤ m, QueueStable lam μ; reason: the proof divides by λ; at λ = 0, W = 1/µ1 − s does not depend on µm for m ≥ 2, so the claim needs λ > 0; a derivative of W is only meaningful where W is finite (both series converge); rates are positive service rates and states start at 1
--   - encoding: ∂W/∂µm < 0 → deriv (fun x => waitFormula lam s (Function.update μ m x)) (μ m) < 0; reason: Mathlib's deriv is 0 at a point of non-differentiability, so the inequality also asserts differentiability, as the paper's derivative presupposes
--   - generalization: W with the shift −v/d (p. 38; a typo for p. 34's −d/v) → an arbitrary real shift s; reason: an additive constant does not change the derivative; the statement specializes to s = d/v
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, proof of Theorem 4, pp. 38–39

import Mathlib
import Definitions.Def_OnDemandRideHailing_CallNoCall_QueueStable
import Definitions.Def_OnDemandRideHailing_CallNoCall_waitFormula

namespace OnDemandRideHailing.CallNoCall

/-- **Proof of Theorem 4: in a state-dependent M/M/k queue, `∂W/∂µm < 0` for every `m`.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, proof of Theorem 4, pp. 38–39: "we show that in a state-dependent M/M/k queue,
the average waiting time `W = Σ_{i=1}^∞ iλ^{i−1}/(µ1µ2···µi) / (1 + Σ_{i=1}^∞ λ^i/(µ1µ2···µi)) − v/d`
is decreasing in `µm` for any `m`, i.e., `∂W/∂µm < 0` for any `m` and `µm`."

Let `λ > 0`, let the service rates `µ_i` be positive for every `i ≥ 1`, and let both series of
the waiting-time formula converge. Then for every state `m ≥ 1`, the waiting time `W`, viewed as
a function of `µm` alone (all other rates fixed), is differentiable at the current value of `µm`
with negative derivative.

**Formalization Note.** `deriv f x < 0` also asserts differentiability, since Lean's `deriv` is
`0` at a point of non-differentiability. `λ > 0` is the proof's own assumption (it writes
`W = (1/λ)(…)`, p. 38); at `λ = 0`, `W = 1/µ1 − d/v` does not depend on `µm` for `m ≥ 2`. The
derivative is only meaningful where `W` is finite, hence `QueueStable`. The shift `s` (printed
`v/d` on p. 38, a typo for p. 34's `d/v`) does not affect the derivative. -/
theorem proof_theorem_4_wait_deriv_neg {lam s : ℝ} {μ : ℕ → ℝ} {m : ℕ}
    (hlam : 0 < lam) (hμ : ∀ i, 1 ≤ i → 0 < μ i) (hm : 1 ≤ m) (hst : QueueStable lam μ) :
    deriv (fun x : ℝ => waitFormula lam s (Function.update μ m x)) (μ m) < 0 := by sorry

end OnDemandRideHailing.CallNoCall

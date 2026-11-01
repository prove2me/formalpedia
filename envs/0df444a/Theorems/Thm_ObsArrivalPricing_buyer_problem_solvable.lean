-- Prove2me | Theorems.Thm_ObsArrivalPricing_buyer_problem_solvable
-- name    : ObsArrivalPricing.buyer_problem_solvable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:42:54.012743+00:00
-- url     : https://prove2.me/theorems/1959390d-ed6c-44e2-b90e-1304412f515c
-- title:
--   p.9 and endnote 1 — the buyer's problem $[BP]$ is solvable
-- statement:
--   Let $\mu>0$ and let $p$ be an admissible price function (lower semicontinuous on $[0,\infty)$, with values in $[0,\bar v]$ there, twice differentiable almost everywhere). A buyer with valuation $v\in\mathbb R$ arrives at time $\tau\ge0$ and solves
--   $$[BP]\qquad \max_{\tau\le t\le\infty}U(t,v),\qquad U(t,v)=e^{-\mu t}(v-p(t)),\quad U(\infty,v)=0,$$
--   purchasing at the earliest maximizer. Then:
--
--   1. the buyer purchases at a finite time (i.e. $[BP]$ has an earliest maximizer $t<\infty$ with $U(t,v)\ge0$) if and only if there exists $\tau_p\in[\tau,\infty)$ with $U(\tau_p,v)\ge0$;
--   2. the purchase time returned by the model is exactly this earliest maximizer: it equals $t$ if and only if $t$ is the earliest finite maximizer.
--
--   Lower semicontinuity of $p$ is what makes the maximum attained, so that the buyer's behaviour, and hence the seller's revenue, is well defined.
--
--   Differences from the source:
--   - encoding: arrival time $\tau\in[0,\infty]$; $\tau=\infty$ never purchases → $\tau\ge0$ finite; reason: an arrival at $\infty$ never meets the seller
--   - generalization: the iff of p.9 together with endnote 1's "the buyer's problem can always be solved" → the iff plus a second clause: the purchase time equals $t$ exactly when $t$ is the earliest maximizer; reason: the added clause states uniqueness of the earliest maximizer; dropping it gives the printed iff
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), §3.1, p.9 ("will purchase (at a finite time) if and only if there exists τp ∈ [τ,∞) such that U(τp,v) ≥ 0"); p.10 (earliest maximizer); endnote 1, p.25

import Mathlib
import Definitions.Def_ObsArrivalPricing_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- The buyer's problem is solvable (Correa, Pizarro & Vulcano, The Value of Observing the Buyer
Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), §3.1, p.9, "a buyer with valuation v
who arrives at time τ will purchase (at a finite time) if and only if there exists τp ∈ [τ,∞) such
that U(τp,v) ≥ 0"; endnote 1, p.25, "the lower semi-continuity is necessary to ensure that the
buyer's problem can always be solved"). For an admissible price function, a buyer arriving at
`τ ≥ 0` has an earliest optimal finite purchase time iff some finite `t ≥ τ` gives nonnegative
utility, and `purchaseTime` returns exactly that time. -/
theorem buyer_problem_solvable {μ vbar : ℝ} (hμ : 0 < μ) {p : ℝ → ℝ}
    (hp : IsAdmissible vbar p) {τ : ℝ} (hτ : 0 ≤ τ) (v : ℝ) :
    ((∃ t, IsPurchase μ p τ v t) ↔ ∃ s, τ ≤ s ∧ 0 ≤ U μ p v s) ∧
      ∀ t, purchaseTime μ p τ v = some t ↔ IsPurchase μ p τ v t := by sorry

end ObsArrivalPricing

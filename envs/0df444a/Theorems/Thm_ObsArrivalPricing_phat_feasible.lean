-- Prove2me | Theorems.Thm_ObsArrivalPricing_phat_feasible
-- name    : ObsArrivalPricing.phat_feasible
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:44.270102+00:00
-- url     : https://prove2.me/theorems/539f6ab0-9bc5-40fe-836c-2cd35246c81e
-- title:
--   Eq. (4), p.18 — the periodic policy $\hat p$ is a feasible price function
-- statement:
--   Let $T>0$ and let $p$ be admissible (lower semicontinuous on $[0,\infty)$, values in $[0,\bar v]$, twice differentiable almost everywhere). Let $\hat p$ be the periodic policy of (4): $\hat p(t)=p(0)$ on $I_{2k-1}=(2(k-1)T,(2k-1)T]$ and $\hat p(t)=p(t-(2k-1)T)$ on $I_{2k}=((2k-1)T,2kT]$, with the value $\min(p(0),p(T))$ at the points $2kT$. Then:
--
--   1. for every $t_0\ge0$ the shifted policy $\hat p_{t_0}(t)=\hat p(t+t_0)$ is an admissible price function;
--   2. if $p$ is right-continuous at $0$, then $\hat p$ is continuous at every point $kT$ with $k\ge1$ odd.
--
--   So $\hat p$, and each of its random shifts, is a feasible price function for the unobservable problem $[SPN]$.
--
--   Differences from the source:
--   - reading: (4): $\hat p(2kT)=p(T)$ → $\hat p(2kT)=\min(p(0),p(T))$; reason: equal for the paper's non-increasing $p$ (p.11); with $p(T)>p(0)$ the printed value would make $\hat p$ fail lower semicontinuity
--   - generalization: $p$ "comes from the solution of $[SPO_0]$" (a continuously differentiable optimum) → every admissible $p$; the continuity clause for every admissible $p$ right-continuous at $0$; reason: a differentiable optimum is admissible and right-continuous at $0$
--   - reading: "feasible pricing policy" → every shift $\hat p_{t_0}$, $t_0\ge0$, belongs to the admissible class of p.9; reason: the class of p.9 is the feasible set of $[SPN]$; the shifts are the policies the paper uses (Figure 2, Proposition 3)
--   - encoding: (4) for $t>0$ only ($k\in\mathbb N$) → $\hat p$ defined on all of $\mathbb R$ by periodicity; reason: values at $t\le0$ only enter through $t_0+t$ with $t\ge 0$, $t_0\ge0$, where they are the periodic value at $0$
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), §5, (4) and the sentence after it, p.18; Figure 2, p.19; Proposition 3, p.20

import Mathlib
import Definitions.Def_ObsArrivalPricing_PeriodicPolicy

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- The periodic policy `p̂` of (4) is a feasible price function (SSRN 3541494, §5, p.18: "The
feasible pricing policy p̂ we consider is periodic …"; "Note that the function p̂ is continuous at
the points kT, for odd values of k"). For `T > 0` and an admissible `p`: every shift
`p̂_{t0}(t) = p̂(t + t0)` with `t0 ≥ 0` is admissible, and if `p` is right-continuous at `0` (as the
paper's differentiable optimal `p` is), `p̂` is continuous at every `kT` with `k` odd. -/
theorem phat_feasible {vbar T : ℝ} (hT : 0 < T) {p : ℝ → ℝ} (hp : IsAdmissible vbar p) :
    (∀ t0 : ℝ, 0 ≤ t0 → IsAdmissible vbar (shiftedPolicy p T t0)) ∧
      (ContinuousWithinAt p (Ici 0) 0 →
        ∀ k : ℕ, 1 ≤ k → ContinuousAt (phat p T) ((2 * k - 1) * T)) := by sorry

end ObsArrivalPricing

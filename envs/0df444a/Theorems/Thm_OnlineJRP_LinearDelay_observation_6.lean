-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_observation_6
-- name    : OnlineJRP.LinearDelay.observation_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:36.660312+00:00
-- url     : https://prove2.me/theorems/0e9eedc8-bada-409b-8d9f-a5fbe03a7cdd
-- title:
--   Observation 6 — $h<\tau_{\min}$, and all earlier purchases are no later than $h$
-- statement:
--   At every call to PlanPurchase in a run, the reference time $h$ chosen by Table 1 satisfies
--   $$
--   h<\tau_{\min},
--   $$
--   and every purchase preceding the call takes place no later than $h$.
--
--   This makes the ghost usage $G(h,\tau_{\min})$ meaningful and its forecast denominator positive.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Observation 6, p. 11

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Observation 6, p. 11 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): at every call to `PlanPurchase`, `h < τmin`, and every purchase preceding the call takes place no later than `h`, where `h` is `st.ref`, chosen by Table 1. -/
theorem observation_6 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l) :
    ∀ st ∈ l, st.phase = .call → st.ref < st.τmin ∧ ∀ b ∈ st.bought, b.1 ≤ st.ref := by sorry

end OnlineJRP.LinearDelay

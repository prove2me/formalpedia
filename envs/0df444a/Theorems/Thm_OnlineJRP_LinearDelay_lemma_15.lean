-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_lemma_15
-- name    : OnlineJRP.LinearDelay.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:45.03111+00:00
-- url     : https://prove2.me/theorems/8a963b97-d33e-4dae-a836-015210852520
-- title:
--   Lemma 15 — after an update with $\tau_{\min}\ge t+H$, the invariant holds with $h:=t$
-- statement:
--   Consider a call to PlanPurchase at time $t$ in a run whose most recent call to UpdateBudgets also occurred at time $t$, with value $H$. If $\tau_{\min}\ge t+H$, then Eq. (6) holds with $h:=t$.
--
--   An intervening purchase at time $t$ is allowed, and the call may be triggered by either kind of event, which is why this one lemma covers rows 1 and 5 of Table 1. It does not use the invariant at any earlier call, and so gives the base case of the induction.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Lemma 15, p. 17

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Lemma 15, p. 17 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): at a call at time `t` whose most recent call to `UpdateBudgets` also occurred at time `t` with value `H`, if `τmin ≥ t + H` then Eq. (6) holds with `h := t`. An intervening purchase at time `t` is allowed, and the call may have either trigger. -/
theorem lemma_15 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l) :
    ∀ st ∈ l, st.phase = .call → ∀ H : ℝ, st.lastUpd = some (st.now, H) →
      st.now + H ≤ st.τmin → InvAt x c st st.now := by sorry

end OnlineJRP.LinearDelay

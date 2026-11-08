-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_observation_2
-- name    : OnlineJRP.LinearDelay.observation_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:10.667947+00:00
-- url     : https://prove2.me/theorems/0d94702f-aeaa-40e9-98c4-69dcd177cdf7
-- title:
--   Observation 2 — effect of UpdateBudgets on budgets, $D$ and $d_i$; $D$ continuous and nondecreasing; Eq. (3)
-- statement:
--   Consider a run of the algorithm and a call to UpdateBudgets at time $t$, with budgets $\alpha_r$, $\alpha'_r$ before and after for a previously revealed request $r$. Then:
--
--   1. $\alpha_r\ge\alpha'_r\ge\min\{\alpha_r,w_r(t-t_r)\}$;
--   2. the call leaves $D(t)$ unchanged, and consequently $D$ along the execution is continuous and nondecreasing;
--   3. revealing the new request does not change $d_i(t)$ for any item $i$;
--   4. for every live request $r$ at item $i$,
--   $$
--   \tau_r-v\ge\frac{c_i-d_i(v)}{W_i}.
--   $$
--
--   These facts underlie the lower bound on OPT and the claim that every active item is mature by its deadline.
--
--   **Formalization Note** Part 4 is stated for every real $v$ at every state of the run, with $d_i(v)$ the state's forecast. Both sides have slope $-1$ in $v$.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
--   - generalization: part 4: at every time v that the request is live → every real v, with d_i(v) the state's forecast; reason: both sides have slope −1 in v, so the claim at all v is the same as at the current time and specializes to the source's at every v at which r is live
--   - reading: D is continuous and nondecreasing → execD l, the forecast at v of the last state of the run with now ≤ v, and 0 if there is none; reason: p. 8 distinguishes D along the execution from a forecast
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Observation 2, p. 6

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Observation 2, p. 6 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)), parts 1–4, for every run at joint cost `1`. Parts 1–3 are for an arrival step from `st` to `st'` at time `t = st'.now` (`α` and `α'` are budgets before and after). The "consequently" of part 2 is about `D` along the execution, `execD l`.

**Formalization Note** Part 4 is stated for every real `v`, not only for `v` at which the request is live: `d_i` is the state's forecast, both sides have slope `-1` in `v`, so this is the same claim as at `now`, and is the form the forecasts need. -/
theorem observation_2 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l) :
    (∀ st ∈ l, ∀ (H : ℝ) (st' : St n), ArrivalStep c σ st H st' →
      (∀ p : Fin st.rev.length,
        st'.α p ≤ st.α p ∧
          min (st.α p) ((st.req p).w * (st'.now - (st.req p).t)) ≤ st'.α p) ∧
      st'.D st'.now = st.D st'.now ∧
      ∀ i, st'.d i st'.now = st.d i st'.now) ∧
    Monotone (execD l) ∧ Continuous (execD l) ∧
    ∀ st ∈ l, ∀ p : Fin st.rev.length, st.svc p = none → ∀ v : ℝ,
      (c (st.req p).i - st.d (st.req p).i v) / st.W (st.req p).i ≤ st.τ p - v := by sorry

end OnlineJRP.LinearDelay

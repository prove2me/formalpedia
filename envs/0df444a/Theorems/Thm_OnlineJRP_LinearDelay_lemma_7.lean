-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_lemma_7
-- name    : OnlineJRP.LinearDelay.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:25.930223+00:00
-- url     : https://prove2.me/theorems/9721d1e1-a87a-405d-9a1b-57341a1e1c0f
-- title:
--   Lemma 7 — the slack forecast in terms of unpaid fees and ghost usage, Eq. (7)
-- statement:
--   At a call to PlanPurchase at time $t$ in a run, with $\rho=1+x$, for every $t\le a\le b\le\tau_{\min}$,
--   $$
--   \mathrm{sl}(b)=\mathrm{sl}(a)+\sum_{i\in[n]}\big(xW_i(b-a)-u_i(a)\big)_++\rho\,G(a,b).
--   $$
--   This identity gives the growth of the slack on the forecast interval: active immature items contribute nothing, mature items contribute at rate $xW_i$, and served requests through the ghost usage.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Lemma 7, Eq. (7), p. 12

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Lemma 7, Eq. (7), p. 12 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): at a call at time `t`, for `t ≤ a ≤ b ≤ τmin`, `sl(b) = sl(a) + ∑_{i ∈ [n]} (x W_i (b - a) - u_i(a))₊ + ρ G(a, b)`, with `ρ = 1 + x`. -/
theorem lemma_7 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l) :
    ∀ st ∈ l, st.phase = .call → ∀ a b : ℝ, st.now ≤ a → a ≤ b → b ≤ st.τmin →
      st.sl x c b = st.sl x c a + ∑ i : Fin n, max (x * st.W i * (b - a) - st.u x c i a) 0 +
        (1 + x) * st.G a b := by sorry

end OnlineJRP.LinearDelay

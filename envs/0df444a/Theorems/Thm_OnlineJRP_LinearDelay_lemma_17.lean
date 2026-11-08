-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_lemma_17
-- name    : OnlineJRP.LinearDelay.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:13.507863+00:00
-- url     : https://prove2.me/theorems/ddffd289-c967-466f-b8ff-341c35d49118
-- title:
--   Lemma 17 — an arrival with $H\ge\tau^-_{\min}-t$ preserves the checkpoint and the ghost usage
-- statement:
--   Consider an arrival at time $t$ with value $H\ge\tau^-_{\min}-t$ that interrupts the plan made at the previous call (superscript minus), with reference time $h^-$. Then $\tau_{\min}=\tau^-_{\min}$ and
--   $$
--   G(h^-,\tau^-_{\min})=G^-(h^-,\tau^-_{\min}),\qquad \mathrm{sl}(\tau^-_{\min})\ge\mathrm{sl}^-(\tau^-_{\min}),\qquad M\ge M^-.
--   $$
--   This gives row 2 of Table 1 from the invariant at the previous call.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Lemma 17, p. 19

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Lemma 17, p. 19 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): for an arrival at time `t` with value `H ≥ τ⁻min - t`, `τmin = τ⁻min`, `G(h⁻, τ⁻min) = G⁻(h⁻, τ⁻min)`, `sl(τ⁻min) ≥ sl⁻(τ⁻min)` and `M ≥ M⁻`.

**Formalization Note** `st'` is the call whose plan the arrival interrupts, and `h⁻` is `st'.ref`. -/
theorem lemma_17 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l)
    {st' st : St n} (hst' : st' ∈ l) {H : ℝ} (har : AfterArrival x c σ st' H st)
    (hH : st'.τmin ≤ st.now + H) :
    st.τmin = st'.τmin ∧ st.G st'.ref st'.τmin = st'.G st'.ref st'.τmin ∧
      st'.sl x c st'.τmin ≤ st.sl x c st'.τmin ∧ st'.M x c ≤ st.M x c := by sorry

end OnlineJRP.LinearDelay

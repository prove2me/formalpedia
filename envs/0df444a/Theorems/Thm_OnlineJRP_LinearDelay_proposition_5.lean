-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_proposition_5
-- name    : OnlineJRP.LinearDelay.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:13.347469+00:00
-- url     : https://prove2.me/theorems/e1c18818-c590-4c92-aba3-103bfc2eb7d7
-- title:
--   Proposition 5 — the invariant (6) at every call to PlanPurchase
-- statement:
--   At every call to PlanPurchase in a run, with the reference time $h$ chosen by Table 1, the fraction below has a positive denominator and
--   $$
--   \mathrm{sl}(\tau_{\min})\ge x+\frac1{x^2}\cdot\frac{G(h,\tau_{\min})}{G(h,\tau_{\min})+M(\tau_{\min}-h)}.
--   $$
--   In particular $\mathrm{sl}(\tau_{\min})\ge x>1$, which is the condition of Observation 4, so this implies the main theorem.
--
--   **Formalization Note** A call is a state before the plan step: the proposition holds without assuming that line 4 of Algorithm 3 finds a time, and it is what proves it does.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
--   - reading: The fraction in (6) is well-defined (the sentence after the proposition) → a first clause of the statement: the denominator is positive; reason: Lean's a / 0 = 0 would otherwise make (6) weaker at a zero denominator
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Proposition 5, Eq. (6), p. 10

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Proposition 5, Eq. (6), p. 10 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): at every call to `PlanPurchase`, with `h` chosen by Table 1, `sl(τmin) ≥ x + (1/x²) · G(h, τmin) / (G(h, τmin) + M (τmin - h))`. The first clause is the paper's next sentence ("The fraction in (6) is well-defined"), and guards against `a / 0 = 0`.

**Formalization Note** A call is a state of phase `call`, before the plan step, so the statement does not assume that line 4 of Algorithm 3 succeeds. -/
theorem proposition_5 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l) :
    ∀ st ∈ l, st.phase = .call →
      0 < st.G st.ref st.τmin + st.M x c * (st.τmin - st.ref) ∧ InvAt x c st st.ref := by sorry

end OnlineJRP.LinearDelay

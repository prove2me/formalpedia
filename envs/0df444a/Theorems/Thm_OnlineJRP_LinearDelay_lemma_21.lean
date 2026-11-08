-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_lemma_21
-- name    : OnlineJRP.LinearDelay.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:22.988128+00:00
-- url     : https://prove2.me/theorems/8f67359f-887a-4ed3-84a9-bd46e385545b
-- title:
--   Lemma 21 — a purchase leaving positive slack happens at the time of an arrival
-- statement:
--   Consider a call following a purchase at time $t$ that leaves a request live, with superscript minus marking the call that planned the purchase. If $\mathrm{sl}(t)>0$, then $t^-=t$, and the previous call is triggered by an arrival at time $t$.
--
--   **Formalization Note** "Triggered by an arrival at time $t$" is: the previous call's trigger is an arrival with some value $H$, and its most recent UpdateBudgets is at time $t$ with the same $H$.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Lemma 21, p. 22

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Lemma 21, p. 22 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): if `sl(t) > 0`, then `t⁻ = t`, and the previous call is triggered by an arrival at time `t`. -/
theorem lemma_21 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l)
    {st' st : St n} (hst' : st' ∈ l) {S : Finset (Fin n)} {s : ℝ}
    (hap : AfterPurchase x c σ st' S s st)
    (hpos : 0 < st.sl x c s) :
    st'.now = s ∧ ∃ H, st'.trig = some (.arrival H) ∧ st'.lastUpd = some (s, H) := by sorry

end OnlineJRP.LinearDelay

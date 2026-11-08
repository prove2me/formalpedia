-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_observation_9
-- name    : OnlineJRP.LinearDelay.observation_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:35.211564+00:00
-- url     : https://prove2.me/theorems/8acda0d2-db5d-4fda-bd63-e8b834c6c5fe
-- title:
--   Observation 9 — the refused item $j$: $u^-_j(\tau^-_{\min})>\widetilde{\mathrm{sl}}$, $\tau^-_j=\tau_j=\tau_{\min}$, $M(\tau_{\min}-\tau^-_{\min})>\widetilde{\mathrm{sl}}$
-- statement:
--   Consider a call following a purchase of $S^-$ at time $t$ that leaves a request live, with superscript minus marking the call that planned the purchase. The refused item $j$, the first item of that call's deadline order outside $S^-$, exists and satisfies:
--
--   1. $u^-_j(\tau^-_{\min})>\widetilde{\mathrm{sl}}$;
--   2. $\tau^-_j=\tau_j=\tau_{\min}$;
--   3. $M(\tau_{\min}-\tau^-_{\min})>\widetilde{\mathrm{sl}}$.
--
--   These bound how soon the next checkpoint can come after a purchase.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
--   - reading: Sec. 4 fixes the case of row 3 of Table 1 and states this for that case → the statement is for every call following a purchase that leaves a request live; reason: Sec. 4.1 opens with properties that hold throughout all purchase cases (p. 13), and Sec. 6 uses them
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Observation 9, p. 13

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Observation 9, p. 13 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): for a call `st` following a purchase of `S⁻` at time `s` planned at the previous call `st'` that leaves a request live, the refused item `j` exists and satisfies a) `u⁻_j(τ⁻min) > s̃l`, b) `τ⁻_j = τ_j = τmin`, c) `M (τmin - τ⁻min) > s̃l`.

**Formalization Note** `st'` is the paper's preceding call (superscript minus). Section 4 fixes the case of row 3 of Table 1, but Sec. 4.1 opens with properties "that hold throughout all purchase cases" (p. 13), and Sec. 6 uses them, so no condition on `sl(t)` or `h⁻` is assumed. -/
theorem observation_9 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l)
    {st' st : St n} (hst' : st' ∈ l) {S : Finset (Fin n)} {s : ℝ}
    (hap : AfterPurchase x c σ st' S s st) :
    ∃ j, st'.refused S = some j ∧
      slTilde x c st' S < st'.u x c j st'.τmin ∧
      st'.τi j = st.τi j ∧ st.τi j = st.τmin ∧
      slTilde x c st' S < st.M x c * (st.τmin - st'.τmin) := by sorry

end OnlineJRP.LinearDelay

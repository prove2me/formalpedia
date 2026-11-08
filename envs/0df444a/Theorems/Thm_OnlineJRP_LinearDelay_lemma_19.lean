-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_lemma_19
-- name    : OnlineJRP.LinearDelay.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:58.026638+00:00
-- url     : https://prove2.me/theorems/13fd4348-bcda-4784-9c2d-b2c7ed89d57b
-- title:
--   Lemma 19 — early purchases: $\mathrm{sl}^-(\tau^-_{\min})>2+1/x^2$
-- statement:
--   Consider a call following a purchase of $S^-$ at time $t$ that leaves a request live, with superscript minus marking the call that planned the purchase. Suppose the invariant (6) holds at every call up to that previous call. If $\mathrm{sl}(t)=0$ and $t<h^-$, then
--   $$
--   \mathrm{sl}^-(\tau^-_{\min})>2+\frac1{x^2}.
--   $$
--   This implies the bound (14) in the case of Table 1's row 4, where the reference time lies in the future of the purchase.
--
--   **Formalization Note** The run is truncated at the previous call. Every run can be so truncated, so no call is lost.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
--   - reading: the printed statement leaves the induction hypothesis implicit (Sec. 3.1, p. 10: assume that the proposition held at all previous calls) → it is an explicit hypothesis, InvAt at every call of the run up to the preceding call (the proof uses it at the pre-call); reason: the proof uses it, and the statement must serve as a step of the proof of Proposition 5; with Proposition 5 it can be discharged
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Lemma 19, p. 20

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Lemma 19, p. 20 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): if `sl(t) = 0` and `t < h⁻`, then `sl⁻(τ⁻min) > 2 + 1/x²`.

**Formalization Note** The hypothesis `hinv` is the induction hypothesis of Sec. 3.1 (p. 10) at every call up to the preceding one `st'`, the run being truncated at `st'`: the proof uses it at the pre-call, two purchases back ("ind. hyp.", Eq. (24)). Every run can be so truncated, so no run is lost. -/
theorem lemma_19 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) {st' st : St n}
    (hl : IsRun x c σ (l ++ [st'])) {S : Finset (Fin n)} {s : ℝ}
    (hap : AfterPurchase x c σ st' S s st)
    (hinv : ∀ st₀ ∈ l ++ [st'], st₀.phase = .call → InvAt x c st₀ st₀.ref)
    (hzero : st.sl x c s = 0) (hh : s < st'.ref) :
    2 + 1 / x ^ 2 < st'.sl x c st'.τmin := by sorry

end OnlineJRP.LinearDelay

-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_lemma_12
-- name    : OnlineJRP.LinearDelay.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:02.280553+00:00
-- url     : https://prove2.me/theorems/da1bc950-7540-43f1-9369-b439cf97ec09
-- title:
--   Lemma 12 — from $h^-$ to $t$: the bound (14)
-- statement:
--   Consider a call following a purchase of $S^-$ at time $t$ that leaves a request live, with superscript minus marking the call that planned the purchase. Suppose the invariant (6) holds at that previous call. If $h^-\le t$ and $t<\tau^-_{\min}$, then
--   $$
--   \mathrm{sl}^-(\tau^-_{\min})\ge x+\frac1{x^2}\cdot\frac{G^-(t,\tau^-_{\min})}{G^-(t,\tau^-_{\min})+(\tau^-_{\min}-t)\sum_{i\in S^-}W^-_i}.
--   $$
--   This restates the lower bound on $\mathrm{sl}^-(\tau^-_{\min})$ in terms of the purchase time rather than the reference time.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
--   - reading: the printed statement leaves the induction hypothesis implicit (Sec. 3.1, p. 10: assume that the proposition held at all previous calls) → it is an explicit hypothesis, InvAt at the preceding call; reason: the proof uses it, and the statement must serve as a step of the proof of Proposition 5; with Proposition 5 it can be discharged
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Lemma 12, Eq. (14), p. 15

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Lemma 12, Eq. (14), p. 15 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): if `h⁻ ≤ t` and `t < τ⁻min`, then the bound (14) holds.

**Formalization Note** The hypothesis `hinv` is the induction hypothesis of Sec. 3.1 ("assume that the proposition held at all previous calls", p. 10), which the printed statement leaves implicit and the proof uses at the preceding call. Combined with Proposition 5, it gives the unconditional form. -/
theorem lemma_12 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l)
    {st' st : St n} (hst' : st' ∈ l) {S : Finset (Fin n)} {s : ℝ}
    (hap : AfterPurchase x c σ st' S s st)
    (hinv : InvAt x c st' st'.ref) (hh : st'.ref ≤ s) (ht : s < st'.τmin) :
    Bound14 x c st' S s := by sorry

end OnlineJRP.LinearDelay

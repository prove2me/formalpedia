-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_lemma_13
-- name    : OnlineJRP.LinearDelay.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:21.759107+00:00
-- url     : https://prove2.me/theorems/ea12f1c4-fd69-4227-b5a0-42e262b93e8d
-- title:
--   Lemma 13 — (14) and $\mathrm{sl}(t)=0$ propagate the invariant with $h:=\tau^-_{\min}$
-- statement:
--   Consider a call following a purchase of $S^-$ at time $t$ that leaves a request live, with superscript minus marking the call that planned the purchase. Suppose the invariant (6) holds at that previous call, that $\mathrm{sl}(t)=0$, and that the bound (14) holds if $t<\tau^-_{\min}$. Then
--   $$
--   \mathrm{sl}(\tau_{\min})\ge x+\frac1{x^2}\cdot\frac{G(\tau^-_{\min},\tau_{\min})}{G(\tau^-_{\min},\tau_{\min})+M(\tau_{\min}-\tau^-_{\min})},
--   $$
--   i.e. Eq. (6) holds with $h:=\tau^-_{\min}$. No assumption $h^-\le t$ is made. This is the step where the exact value of $x$ is used.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
--   - reading: the printed statement leaves the induction hypothesis implicit (Sec. 3.1, p. 10: assume that the proposition held at all previous calls) → it is an explicit hypothesis, InvAt at the preceding call; reason: the proof uses it, and the statement must serve as a step of the proof of Proposition 5; with Proposition 5 it can be discharged
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Lemma 13, p. 16

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Lemma 13, p. 16 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): if `sl(t) = 0` and, if `t < τ⁻min`, the bound (14) holds, then Eq. (6) holds with `h := τ⁻min`.

**Formalization Note** The hypothesis `hinv` is the induction hypothesis of Sec. 3.1 (p. 10), which the proof uses as "ind. hyp." at the preceding call. As printed there is no assumption `h⁻ ≤ t`: Sec. 6 uses this lemma when `h⁻ > t`. -/
theorem lemma_13 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l)
    {st' st : St n} (hst' : st' ∈ l) {S : Finset (Fin n)} {s : ℝ}
    (hap : AfterPurchase x c σ st' S s st)
    (hinv : InvAt x c st' st'.ref) (hzero : st.sl x c s = 0)
    (h14 : s < st'.τmin → Bound14 x c st' S s) :
    InvAt x c st st'.τmin := by sorry

end OnlineJRP.LinearDelay

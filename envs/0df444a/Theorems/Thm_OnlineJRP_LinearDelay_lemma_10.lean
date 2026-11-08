-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_lemma_10
-- name    : OnlineJRP.LinearDelay.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:13.043188+00:00
-- url     : https://prove2.me/theorems/cfaad094-d909-4f2a-b8eb-524d170d6cfd
-- title:
--   Lemma 10 — actual vs. virtual purchase, Eqs. (8)–(11)
-- statement:
--   Consider a call following a purchase of $S^-$ at time $t$ that leaves a request live, with superscript minus marking the call that planned the purchase, and $\rho=1+x$. Then
--   $$
--   \widetilde{\mathrm{sl}}=\mathrm{sl}(t)+x(\tau^-_{\min}-t)\sum_{i\in S^-}W^-_i+\rho\,G^-(t,\tau^-_{\min}),
--   $$
--   $$
--   \mathrm{sl}(t)\le\widetilde{\mathrm{sl}}\le\mathrm{sl}^-(\tau^-_{\min})-1,\qquad G(\tau^-_{\min},\tau_{\min})\ge\mathrm{sl}^-(\tau^-_{\min})-1-\widetilde{\mathrm{sl}},
--   $$
--   $$
--   \mathrm{sl}(\tau_{\min})\ge x\widetilde{\mathrm{sl}}+(\tau^-_{\min}-t)\sum_{i\in S^-}W^-_i+\rho\,G(\tau^-_{\min},\tau_{\min}).
--   $$
--   These compare the actual purchase with a virtual purchase of the same set at the checkpoint, and propagate slack to the next checkpoint.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
--   - reading: Sec. 4 fixes the case of row 3 of Table 1 and states this for that case → the statement is for every call following a purchase that leaves a request live; reason: Sec. 4.1 opens with properties that hold throughout all purchase cases (p. 13), and Sec. 6 uses them
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Lemma 10, Eqs. (8)–(11), p. 13

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Lemma 10, Eqs. (8)–(11), p. 13 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)), for a call `st` following a purchase of `S⁻` at time `t = s` planned at the previous call `st'` that leaves a request live, with `ρ = 1 + x`.

**Formalization Note** As for Observation 9, no condition on `sl(t)` or `h⁻` is assumed: these are properties "that hold throughout all purchase cases" (p. 13). -/
theorem lemma_10 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l)
    {st' st : St n} (hst' : st' ∈ l) {S : Finset (Fin n)} {s : ℝ}
    (hap : AfterPurchase x c σ st' S s st) :
    slTilde x c st' S = st.sl x c s + x * (st'.τmin - s) * ∑ i ∈ S, st'.W i +
        (1 + x) * st'.G s st'.τmin ∧
      st.sl x c s ≤ slTilde x c st' S ∧
      slTilde x c st' S ≤ st'.sl x c st'.τmin - 1 ∧
      st'.sl x c st'.τmin - 1 - slTilde x c st' S ≤ st.G st'.τmin st.τmin ∧
      x * slTilde x c st' S + (st'.τmin - s) * (∑ i ∈ S, st'.W i) +
          (1 + x) * st.G st'.τmin st.τmin ≤ st.sl x c st.τmin := by sorry

end OnlineJRP.LinearDelay

-- Prove2me | Theorems.Thm_OnlineJRP_LinearDelay_lemma_3
-- name    : OnlineJRP.LinearDelay.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:04.055781+00:00
-- url     : https://prove2.me/theorems/15c25c57-dd37-4de4-9b7f-db5948f84065
-- title:
--   Lemma 3 — a suitable $H>0$ exists, and $D(t)\le\mathrm{OPT}$
-- statement:
--   At a ready state of a run, for an eligible next request, there is $H>0$ with $\Phi(H)=1$, i.e. Eq. (2) can be satisfied and UpdateBudgets is well defined. Moreover, for every time $t$,
--   $$
--   D(t)\le\mathrm{OPT},
--   $$
--   where $D$ is along the execution and $\mathrm{OPT}$ is the offline optimum of the whole input at joint cost $1$.
--
--   This is the lower bound on the optimum against which the algorithm charges its cost.
--
--   Differences from the source:
--   - encoding: the event loop of Algorithm 1, requests identified as objects, a call to a subroutine as an instant → the relation IsRun on lists of states, list positions in rev as the identity of a request, a call to PlanPurchase as a state of phase call before the plan step, τ⁻min = ∞ as lastCk = none; reason: a trace makes the previous calls available; the statement about a call must not assume that line 4 of Algorithm 3 succeeds
--   - reading: Choose any H > 0 satisfying (2) → every run, with any admissible H at every arrival; reason: the milestones concern the algorithm for every choice the page allows
--   - reading: the sum over r with t_r ≤ t in (2) and D(t) → the sum over the requests revealed so far; reason: Algorithm 2 line 2 says every revealed request, and a request released at time t but not yet processed has no budget yet
--   - reading: S := {i : u_i(τmin) = 0} ∪ {i_1, …, i_m} → the first set is read over active items; reason: the page calls S the set of all items that reach maturity, and M on p. 10 is over active items; an inactive item with c_i = 0 would otherwise be a spurious member
--   - reading: Table 1, rows 3–5, conditions sl(t) = 0 and sl(t) > 0 → h := τ⁻min if sl(t) = 0, else h := t; reason: rows 3 and 4 share h, and sl(t) < 0 is unreachable since the purchase is affordable
--   - reading: D(t) ≤ OPT → execD l t ≤ OPT, for every run prefix l and every real t, with OPT of the whole input; reason: p. 8 distinguishes D along the execution from a forecast; a prefix of a run is a run on the prefix of the input, whose OPT is at most that of the whole input
--   - reading: there exists H > 0 satisfying (2) → at each ready state of a run whose next request is released before the planned purchase, or with no plan; reason: those are the states at which Algorithm 1 calls UpdateBudgets
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Lemma 3, p. 6

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_InvAt

namespace OnlineJRP.LinearDelay

/-- Lemma 3, p. 6 (Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…)): at a ready state with an eligible next request `r`, there exists `H > 0` satisfying Eq. (2); and `D(t) ≤ OPT` for every time `t`.

**Formalization Note** `D` is `execD l`, the value along the execution, and `OPT` is that of the whole input `σ` at joint cost `1`. -/
theorem lemma_3 {n : ℕ} (x : ℝ) (hx : x * (x - 1) ^ 2 = 1) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (σ : List (Req n)) (hσ : IsInstance σ) (l : List (St n)) (hl : IsRun x c σ l) :
    (∀ st ∈ l, st.phase = .ready → ∀ r, σ[st.rev.length]? = some r →
      (∀ S s, st.plan = some (S, s) → r.t < s) → ∃ H, 0 < H ∧ st.Phi c r H = 1) ∧
    ∀ t : ℝ, execD l t ≤ OPT ⟨1, c, one_pos, hc⟩ σ := by sorry

end OnlineJRP.LinearDelay

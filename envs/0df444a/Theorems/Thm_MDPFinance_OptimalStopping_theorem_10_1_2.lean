-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_1_2
-- name    : MDPFinance.OptimalStopping.theorem_10_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:41:50.340369+00:00
-- url     : https://prove2.me/theorems/dbb18708-341f-4c77-863a-050eec59c929
-- title:
--   Theorem 10.1.2 — a stopping problem is a Markov Decision Problem
-- statement:
--   **Theorem 10.1.2** (p. 306). It holds that
--
--   a) $V_0(x) = V_N^*(x)$ for all $x \in E$.
--   b) Suppose $\pi^* = (f_0^*,\dots,f_{N-1}^*)$ is an optimal policy for the Markov Decision Problem
--      and define the stopping time $\tau^* := \inf\{n \in \mathbb{N}_0 \mid f_n^*(X_n) = 1\} \wedge N$;
--      then $\tau^*$ is optimal for the stopping problem **(10.1)**.
--
--   This is the bridge the whole chapter rests on: a stopping problem *is* an absorbing Markov
--   Decision Problem with $A = \{0,1\}$, so Chapter 2's machinery applies to it.
--
--   a) is not a tautology in either direction, and both directions are the content. $V_0$ is a
--   supremum over **Markov** policies $(f_n)$ — each $f_n$ looks only at $X_n$ — while $V_N^*$ is a
--   supremum over **all** stopping times, which are in general history-dependent
--   ($\mathbf 1_{[\tau=n]} = f_n(X_0,\dots,X_n)$, p. 305). That the two agree says the extra history
--   buys nothing.
--
--   b)'s cap $\wedge N$ is load-bearing: without it $\inf\emptyset = \infty$ and $\tau^*$ would not be
--   a stopping time bounded by $N$.
--
--   **Moderation note.** Restated on the corrected values: a) the value over measurable Markov policies equals `V_N^*` (both `[-∞,∞]`-valued suprema, no `IsLUB`/`Integrable` devices); b) an optimal Markov policy's stopping time is optimal for (10.1).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 306 (PDF 314), Theorem 10.1.2

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_StoppingProblem

open MeasureTheory

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.1.2** (p. 306). a) `V_0(x) = V_N^*(x)` for all `x`: the value over Markov
policies of the associated Markov Decision Model equals the value **(10.1)** over all stopping
times. b) If `π^* = (f_0^*,…,f_{N-1}^*)` is an optimal policy, `τ^* := inf{n | f_n^*(X_n) = 1} ∧ N`
is an optimal stopping time for **(10.1)**. -/
theorem theorem_10_1_2 {E : Type*} [MeasurableSpace E] {N : ℕ} (P : StoppingProblem E N)
    (Pr : ℕ → E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr) :
    (∀ x : E, P.policyValue Pr x = P.Vn Pr 0 x) ∧
    (∀ S : ℕ → Set E, (∀ n, MeasurableSet (S n)) →
      (∀ x : E, P.EReward Pr 0 (policyTime S N) x = P.policyValue Pr x) →
      IsStopTime (policyTime S N) ∧ (∀ w : ℕ → E, policyTime S N w ≤ (N : ℕ∞)) ∧
        ∀ x : E, P.EReward Pr 0 (policyTime S N) x = P.Vn Pr 0 x) := by sorry

end MDPFinance.OptimalStopping

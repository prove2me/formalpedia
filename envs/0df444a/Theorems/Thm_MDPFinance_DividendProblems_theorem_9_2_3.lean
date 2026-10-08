-- Prove2me | Theorems.Thm_MDPFinance_DividendProblems_theorem_9_2_3
-- name    : MDPFinance.DividendProblems.theorem_9_2_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:13:50.043308+00:00
-- url     : https://prove2.me/theorems/86460ac6-6bbb-4b97-8f3b-c16ee77d945d
-- title:
--   Theorem 9.2.3 — value-function bounds and a Lipschitz-type property
-- statement:
--   Three basic properties of the dividend model's value function and its largest-maximizer optimal policy $f^*$: explicit two-sided bounds on $J_\infty(x)$ in terms of $\mathbb EZ^+$; monotonicity together with the Lipschitz-type inequality $J_\infty(x)-J_\infty(y) \ge x-y$ (paying the whole gap $x-y$ immediately can never do better than the optimal policy from $y$); and a self-consistency identity showing that after paying $f^*(x)$, the post-payment state $x-f^*(x)$ is itself a state where paying nothing is optimal. This last fact is the technical seed every later structural result (finiteness of $\xi$, the increment property, the goal itself) grows from.
--
--   **Moderation note.** Restated in `[0,∞]` on the corrected `J_∞` (the draft's real `J_∞` was identically `0`, see `StationaryMDM`): the two-sided bounds, monotonicity with `J_∞(y) + (x − y) ≤ J_∞(x)`, and `f^*(x − f^*(x)) = 0`, `J_∞(x) = f^*(x) + J_∞(x − f^*(x))`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 274, PDF 284, Theorem 9.2.3

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Theorem 9.2.3 (Bäuerle–Rieder, p. 274, PDF 284). a) `x + \beta\mathbb EZ^+/(1-\beta q^+) \le
J_\infty(x) \le x + \beta\mathbb EZ^+/(1-\beta)` for `x \ge 0`. b) `J_\infty` is increasing and
`J_\infty(x) - J_\infty(y) \ge x - y` for `x \ge y \ge 0`. c) `f^*(x - f^*(x)) = 0` and
`J_\infty(x) - f^*(x) = J_\infty(x - f^*(x))` for `x \ge 0`, `f^*` the largest maximizer of
`J_\infty`. Stated in `[0,\infty]` (`J_\infty` is finite by Lemma 9.2.2). -/
theorem theorem_9_2_3 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ x : ℤ, 0 ≤ x →
        ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β * M.qplus)) ≤ M.Jinf x ∧
          M.Jinf x ≤ ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β))) ∧
      (Monotone M.Jinf ∧
        ∀ x y : ℤ, 0 ≤ y → y ≤ x → M.Jinf y + ((x - y).toNat : ℝ≥0∞) ≤ M.Jinf x) ∧
      (∀ x : ℤ, 0 ≤ x → fstar (x - (fstar x : ℤ)) = 0 ∧
        M.Jinf x = (fstar x : ℝ≥0∞) + M.Jinf (x - (fstar x : ℤ))) := by sorry

end MDPFinance.DividendProblems

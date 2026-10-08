-- Prove2me | Theorems.Thm_MyersonBargaining_NashSolution_bargaining_solution_existsUnique
-- name    : MyersonBargaining.NashSolution.bargaining_solution_existsUnique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:38.19465+00:00
-- url     : https://prove2.me/theorems/b3a283ef-59c5-4630-a371-cfc09c60a9ec
-- title:
--   Theorem 3 — the incentive-feasible bargaining solution exists and is unique
-- statement:
--   Fix a finite Bayesian collective choice problem $G$ and a conflict choice $c^*$. Suppose the mechanism that always selects $c^*$ is not incentive-efficient. Then there is exactly one interim payoff vector $x$ in the individually rational incentive-feasible set $F^*_+$ that maximizes the generalized Nash product:
--
--   $$
--   \exists!x\in F^*_+\quad\forall y\in F^*_+,\qquad
--   \prod_i\prod_{a_i\in A_i}(y_{i,a_i}-t_{i,a_i})^{R_i(a_i)}
--   \le
--   \prod_i\prod_{a_i\in A_i}(x_{i,a_i}-t_{i,a_i})^{R_i(a_i)}.
--   $$
--
--   The unique object is the payoff vector, and multiple choice mechanisms can implement it. The hypothesis is the paper's non-efficiency condition on the conflict outcome; it implies that some incentive-feasible vector strictly improves every conflict payoff.
--
--   The paper's parenthesis ("so that $t$ is strictly dominated in $F^*$") is not a separate hypothesis: the constant-$c^*$ mechanism is always a Bayesian incentive-compatible choice mechanism, so its failing to be incentive-efficient is the same as $t$ being strictly dominated in $F^*$. The paper's proof says the log of the Nash product is "strictly convex"; it is strictly concave, a printed slip that does not affect the statement.
--
--   **Formalization Note** All player and type sets are finite and nonempty, and every marginal type probability $R_i(a_i)$ is positive. This makes the conditional probabilities and the positive exponents in the Nash product well defined.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), p. 69, Theorem 3 and Eq. (18)

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Theorem 3, p. 69: the incentive-feasible Nash-product maximizer exists uniquely. -/
theorem bargaining_solution_existsUnique
    (G : Problem ι A C) (cstar : C)
    (h : ¬ IsIncentiveEfficient G (constMech (A := A) cstar)) :
    ∃! x : (Σ i, A i) → ℝ, IsBargainingSolution G cstar x := by sorry

end MyersonBargaining.NashSolution

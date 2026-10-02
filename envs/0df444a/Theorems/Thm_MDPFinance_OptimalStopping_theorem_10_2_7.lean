-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_2_7
-- name    : MDPFinance.OptimalStopping.theorem_10_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:45:18.610363+00:00
-- url     : https://prove2.me/theorems/2943d17e-66b7-49e1-be4e-4ec5850cda01
-- title:
--   Theorem 10.2.7 — the One-Step-Look-Ahead Rule
-- statement:
--   **Theorem 10.2.7** (p. 316), the **One-Step-Look-Ahead Rule**. Suppose a stopping problem
--   is given. Let
--   $$ S_0 := \Big\{x \in E \ \Big|\ g(x) \ge c(x) + \beta\int g(x')Q^X(dx'|x)\Big\} $$
--   be **closed**, i.e. $Q^X(S_0|x) = 1$ for all $x \in S_0$. Then it holds:
--
--   a) The decision rule $f^* = \mathbf 1_{S_0}$ is a maximizer of $J_n$, $n \in \mathbb{N}$, and also
--      of $J$.
--   b) Define $\tau^* := \inf\{n \in \mathbb{N}_0 \mid X_n \in S_0\}$. Then $\tau^* \wedge N$ is
--      optimal for the $N$-stage stopping problem. If $\mathbb{P}_x(\tau^* < \infty) = 1$ for all
--      $x \in E$, then $\tau^*$ is optimal for the unbounded stopping problem.
--
--   The rule is myopic — "it compares the reward which is obtained when we stop immediately with the
--   reward when we stop one step ahead" — and the theorem says that under one structural condition the
--   myopic rule is globally optimal.
--
--   **Closedness of $S_0$ is the entire hypothesis and is not a regularity condition.** Once the chain
--   has entered $S_0$ it can never leave, so looking one step ahead is the same as looking arbitrarily
--   far ahead. Without it the rule is genuinely suboptimal and the statement would be false.
--
--   Note the different strength of b)'s two halves: for the $N$-stage problem $\tau^* \wedge N$ is
--   optimal unconditionally, while for the unbounded problem almost sure finiteness of $\tau^*$ is an
--   extra hypothesis.
--
--   **Moderation note.** `S_0` is defined with the `[-∞,∞]`-valued integral of `g`; a) for `n ≥ 1` (the book's `n ∈ ℕ`); b) as attainment of the `N`-stage value and `IsOptimal` for the unbounded problem.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 316 (PDF 323), Theorem 10.2.7

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.2.7** (p. 315), the **One-Step-Look-Ahead Rule**, under (B). Let
`S_0 := {x | g(x) ≥ c(x) + β ∫ g dQ^X(·|x)}` be closed (`Q^X(S_0|x) = 1` for `x ∈ S_0`). Then
a) `f^* = 1_{S_0}` is a maximizer of every `J_n`, `n ≥ 1`, and of `J`; b) with `τ^* := inf{n |
X_n ∈ S_0}`, `τ^* ∧ N` is optimal for the `N`-stage problem, and if `ℙ_x(τ^* < ∞) = 1` for all
`x` then `τ^*` is optimal for the unbounded problem. -/
theorem theorem_10_2_7 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (S0 : Set E)
    (hS0 : S0 = {x : E | (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (P.g y : EReal)) ≤ (P.g x : EReal)})
    (hclosed : ∀ x ∈ S0, P.QX x S0 = 1) :
    (P.IsMaximizer S0 P.Jlim ∧ ∀ n : ℕ, 1 ≤ n → P.IsMaximizer S0 (P.J n)) ∧
    ((∀ (N : ℕ) (x : E), P.EReward Pr (truncTime (hitTime S0) N) x = P.valueUpTo Pr N x) ∧
      ((∀ x : E, Pr x {w | hitTime S0 w = ⊤} = 0) → P.IsOptimal Pr (hitTime S0))) := by sorry

end MDPFinance.OptimalStopping

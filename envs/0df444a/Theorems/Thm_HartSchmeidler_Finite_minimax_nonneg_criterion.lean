-- Prove2me | Theorems.Thm_HartSchmeidler_Finite_minimax_nonneg_criterion
-- name    : HartSchmeidler.Finite.minimax_nonneg_criterion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:33:32.871994+00:00
-- url     : https://prove2.me/theorems/4a7bb6b3-95a9-4ac8-b49d-c98b87a1db2f
-- title:
--   Proof of Theorem 1 — nonnegative minimax criterion
-- statement:
--   Let $X$ and $Y$ be finite, nonempty pure-strategy sets and $A:X\times Y\to\mathbb R$ a payoff matrix. Suppose that against every lottery $y$ on $Y$, the maximizing player has some lottery $x$ on $X$ whose expected payoff is nonnegative:
--
--   $$
--   \forall y\in\Delta(Y),\ \exists x\in\Delta(X):
--      \sum_{a\in X}\sum_{b\in Y}x(a)y(b)A(a,b)\ge0.
--   $$
--
--   Then one lottery $x$ guarantees nonnegative expected payoff against every lottery $y$ on $Y$. This is the criterion for the auxiliary game that Hart and Schmeidler draw from the finite minimax theorem.
--
--   **Formalization Note** Both pure-strategy sets are nonempty so that their lottery sets exist. The paper's auxiliary game has this property when there is at least one player; the playerless boundary of the goal requires its own immediate case.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 19, proof of Theorem 1 (‘By the Minimax Theorem’); https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_agt_games
import Mathlib

namespace HartSchmeidler.Finite

open Finset

/-- Proof of Theorem 1, p. 19: the finite minimax theorem turns a response
to each column lottery into one row lottery guaranteeing nonnegative payoff. -/
theorem minimax_nonneg_criterion {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (A : X → Y → ℝ)
    (hA : ∀ y : Y → ℝ, AGT.IsLottery y →
      ∃ x : X → ℝ, AGT.IsLottery x ∧
        0 ≤ ∑ a, ∑ b, x a * y b * A a b) :
    ∃ x : X → ℝ, AGT.IsLottery x ∧
      ∀ y : Y → ℝ, AGT.IsLottery y →
        0 ≤ ∑ a, ∑ b, x a * y b * A a b := by sorry

end HartSchmeidler.Finite

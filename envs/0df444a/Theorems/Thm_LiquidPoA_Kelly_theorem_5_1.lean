-- Prove2me | Theorems.Thm_LiquidPoA_Kelly_theorem_5_1
-- name    : LiquidPoA.Kelly.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:10.502913+00:00
-- url     : https://prove2.me/theorems/f55facae-3cd4-4660-9dc8-d407c61f3b4a
-- title:
--   Theorem 5.1, p. 14 — the liquid price of anarchy of Kelly is exactly 2
-- statement:
--   For every number $n\ge2$ of players, the liquid price of anarchy of the Kelly proportional allocation mechanism is exactly two:
--
--   $$
--   LPoA(Kelly_n)=2.
--   $$
--
--   The supremum ranges over every admissible budgeted resource allocation game and every pure Nash equilibrium, including signal vectors outside $\mathbb X_n$. It is the paper's tight efficiency statement for Kelly.
--
--   **Formalization Note** Kelly charges each player's submitted signal at every profile, as specified on p. 9. Liquid welfare, budgets, and suprema are extended nonnegative reals. The paper's one-player case has a different value, so $n\ge2$ is explicit.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, p. 14, Theorem 5.1; proof p. 15

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Theorem 5.1, p. 14: the full liquid price of anarchy of Kelly is exactly two. -/
theorem theorem_5_1 (n : ℕ) (hn : 2 ≤ n) :
    lpoa (kelly n) = 2 := by sorry

end LiquidPoA.Kelly

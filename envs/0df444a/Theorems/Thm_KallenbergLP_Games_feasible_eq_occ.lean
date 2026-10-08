-- Prove2me | Theorems.Thm_KallenbergLP_Games_feasible_eq_occ
-- name    : KallenbergLP.Games.feasible_eq_occ
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:56:39.90701+00:00
-- url     : https://prove2.me/theorems/580c9a0e-10e3-4517-bfc8-d22bd4fed241
-- title:
--   Theorem 6.2.4 (ii) — every feasible (x, z) of (6.2.2) has x = x(π) and z ≤ z(π) for π = x / Σ_a x
-- statement:
--   Let $(E,A,B,p,r)$ be a stochastic game satisfying Assumptions 6.2.1 and 6.2.2, and let $\beta_j > 0$, $j \in E$. If $(x,z)$ is a feasible solution of the linear program (6.2.2) and
--   $$\pi_{ia} := x_{ia}\Big/\sum_a x_{ia}, \qquad a \in A(i),\ i \in E,$$
--   then $\pi$ is a stationary decision rule of player I, and
--   $$x = x(\pi), \qquad z \le z(\pi)$$
--   (componentwise), with $x(\pi)$, $z(\pi)$ as in Theorem 6.2.4 (i).
--
--   So every feasible point of (6.2.2) is dominated by the point $(x(\pi),z(\pi))$ of a stationary policy.
--
--   **Formalization Note** The book's "$x = x(\pi)$" presupposes that $\pi$ is a stationary policy (it defines $x(\pi)$ only for those); the Lean statement makes this an explicit part of the conclusion.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 198, Theorem 6.2.4 (ii) (Assumptions 6.2.1, 6.2.2 and β_j > 0 standing, pp. 192–194)

import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController

namespace KallenbergLP.Games

/-- Theorem 6.2.4 (ii) (p. 198): under Assumptions 6.2.1 and 6.2.2, with `β ≫ 0`, if `(x, z)` is
feasible for (6.2.2) and `π_{ia} := x_{ia} / ∑_a x_{ia}`, then `π` is a stationary decision rule
for player I, `x = x(π)` and `z ≤ z(π)`. -/
theorem feasible_eq_occ {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) (hC : Assumption622 G)
    (β' : Fin N → ℝ) (hβ : ∀ j, 0 < β' j)
    (x : Fin N → α → ℝ) (z : Fin N → ℝ) (hxz : LP622Feasible G β' x z) :
    IsDecisionRule1 G (piOfX G x) ∧ x = occ G β' (piOfX G x) ∧ z ≤ zval G β' (piOfX G x) := by sorry

end KallenbergLP.Games

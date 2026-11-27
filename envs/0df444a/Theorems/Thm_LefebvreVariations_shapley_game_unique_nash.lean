-- Prove2me | Theorems.Thm_LefebvreVariations_shapley_game_unique_nash
-- name    : LefebvreVariations.shapley_game_unique_nash
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:21:36.033535+00:00
-- url     : https://prove2.me/theorems/c6ffe6a8-8173-4357-b877-46808a8761ab
-- title:
--   Lefebvre's variations, No. 260 — on a theme by Shapley: Shapley's three-by-three game has the uniform pair as its only Nash equilibrium
-- statement:
--   In the bimatrix game with row payoffs $A_{ij}=[\,i=j\,]$ and column payoffs $B_{ij}=[\,j=i+1 \bmod 3\,]$ on $\{0,1,2\}^2$, a pair of mixed strategies $(x,y)$ is a Nash equilibrium if and only if $x=y=(\tfrac13,\tfrac13,\tfrac13)$:
--   $$\Big(x,y\in\Delta_2,\ \ \forall k:\ (Ay)_k\le x^{\!\top\!}Ay,\ \ \forall l:\ (x^{\!\top\!}B)_l\le x^{\!\top\!}By\Big)\iff x=y=\big(\tfrac13,\tfrac13,\tfrac13\big).$$
--
--   This is the Shapley game, in which the row player wants to match and the column player wants to play one step ahead. It has no pure equilibrium and a unique completely mixed one, and fictitious play does not converge to it: the empirical frequencies cycle around the equilibrium on ever longer runs.
--
--   **Formalization Note** The indices are \texttt{Fin 3} with addition mod $3$; the equilibrium conditions say that each pure strategy of a player earns at most the equilibrium payoff against the opponent's mixed strategy. Mixed strategies are real vectors with nonnegative entries summing to $1$.
--
--   **Why this is a variation.** No open platform problem on Shapley's game itself was found; platform problems on fictitious play (e.g. the ArbSlowFP and StochFictPlay families) concern convergence of the learning dynamics. This statement is the equilibrium of the game on which fictitious play cycles: a finite, explicit uniqueness claim checked by support enumeration. No formal link to a platform parent is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   L. S. Shapley, "Some topics in two-person games", in Advances in Game Theory, Annals of Mathematics Studies 52 (1964), 1-28: the 3x3 game on which fictitious play fails to converge (matrices cited from memory). Uniqueness of the equilibrium was verified here by support enumeration over all 3x3 supports with exact linear solves in floating point (only the uniform pair survives, no singular support).

import Mathlib

namespace LefebvreVariations

/-- Shapley's `3 × 3` game has exactly one Nash equilibrium, the uniform one. Row payoffs are
`A i j = [i = j]`, column payoffs are `B i j = [j = i + 1]` (indices mod 3). A pair of mixed
strategies `x`, `y` is an equilibrium iff each pure strategy of a player earns at most the
equilibrium payoff against the opponent's mixed strategy; the only such pair is
`x = y = (1/3, 1/3, 1/3)`, and it is one. Source: L. S. Shapley, *Some topics in two-person games*,
Advances in Game Theory, Ann. of Math. Stud. 52 (1964), the game on which fictitious play cycles
(matrices cited from memory). -/
theorem shapley_game_unique_nash (x y : Fin 3 → ℝ) :
    ((∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 ∧ (∀ j, 0 ≤ y j) ∧ ∑ j, y j = 1 ∧
      (∀ k, ∑ j, (if k = j then (1 : ℝ) else 0) * y j ≤
        ∑ i, ∑ j, x i * (if i = j then (1 : ℝ) else 0) * y j) ∧
      (∀ l, ∑ i, x i * (if l = i + 1 then (1 : ℝ) else 0) ≤
        ∑ i, ∑ j, x i * (if j = i + 1 then (1 : ℝ) else 0) * y j)) ↔
    (x = fun _ => 1 / 3) ∧ (y = fun _ => 1 / 3) := by
  sorry

end LefebvreVariations

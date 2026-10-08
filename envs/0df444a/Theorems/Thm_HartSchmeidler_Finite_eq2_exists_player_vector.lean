-- Prove2me | Theorems.Thm_HartSchmeidler_Finite_eq2_exists_player_vector
-- name    : HartSchmeidler.Finite.eq2_exists_player_vector
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:51:06.666982+00:00
-- url     : https://prove2.me/theorems/99a17299-844a-4abb-b655-2ec07cadb4c6
-- title:
--   Equation (2) — a playerwise probability vector
-- statement:
--   Fix a player $i$ of a finite game and any nonnegative array $y^i(r^i,t^i)$ indexed by two pure strategies of that player. There is a probability vector $x^i$ on $S^i$ such that, for every fixed profile $s^{-i}$ of the other players,
--
--   $$
--   \sum_{r^i\in S^i}x^i(r^i)\sum_{t^i\in S^i}y^i(r^i,t^i)
--     \bigl[h^i(s^{-i},r^i)-h^i(s^{-i},t^i)\bigr]=0.
--   $$
--
--   This is equation (2), the playerwise cancellation used before forming the product strategy.
--
--   **Formalization Note** The array is merely nonnegative: a slice of player II's single lottery over all triples need not itself sum to one. A full profile supplies $s^{-i}$, and both payoff terms replace its $i$th coordinate, so their values do not depend on its original $i$th coordinate.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 20, proof of Theorem 1, equation (2); https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Finite_Game

namespace HartSchmeidler.Finite

open Finset

/-- Equation (2), p. 20: the lemma supplies a lottery on one player's
strategies for every nonnegative slice of player II's strategy. -/
theorem eq2_exists_player_vector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]
    [∀ j, Nonempty (S j)] (h : ι → (∀ j, S j) → ℝ)
    (i : ι) (y : S i → S i → ℝ) (hy : ∀ r t, 0 ≤ y r t) :
    ∃ x : S i → ℝ, AGT.IsLottery x ∧
      ∀ s : ∀ j, S j,
        ∑ r, x r * ∑ t, y r t *
          (h i (Function.update s i r) - h i (Function.update s i t)) = 0 := by sorry

end HartSchmeidler.Finite

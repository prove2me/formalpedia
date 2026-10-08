-- Prove2me | Theorems.Thm_HartSchmeidler_Finite_correlated_equilibrium_exists
-- name    : HartSchmeidler.Finite.correlated_equilibrium_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:51:19.276123+00:00
-- url     : https://prove2.me/theorems/1fb65b92-47f8-4e86-add6-46043bc5a1ad
-- title:
--   Theorem 1 — every finite game has a correlated equilibrium
-- statement:
--   Let $N$ be a finite set of players. For every $i\in N$, let $S^i$ be a finite, nonempty set of pure strategies, and let $h^i:S\to\mathbb R$ be an arbitrary real payoff function on $S=\prod_{j\in N}S^j$. There exists a probability vector $p$ on $S$ satisfying the correlated-equilibrium incentive inequalities:
--
--   $$
--   \forall i\in N\ \forall r^i,t^i\in S^i,\qquad
--   \sum_{s^{-i}\in S^{-i}}p(s^{-i},r^i)
--     \bigl[h^i(s^{-i},r^i)-h^i(s^{-i},t^i)\bigr]\ge0.
--   $$
--
--   This is Hart and Schmeidler's finite-game existence theorem, which supplies the finite core for their later infinite-game results.
--
--   **Formalization Note** Each strategy set must be nonempty to admit a probability vector. An empty player set is allowed: its profile set has one element and the incentive conditions have no instances. Finiteness and decidable equality are Lean enumeration requirements; payoffs have no sign or normalization restriction.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 19, Theorem 1 and condition (1); https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Finite_Game

namespace HartSchmeidler.Finite

/-- Theorem 1, p. 19: every finite game has a correlated equilibrium in
the sense of condition (1). -/
theorem correlated_equilibrium_exists {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)] (h : ι → (∀ i, S i) → ℝ) :
    ∃ p : (∀ i, S i) → ℝ, IsCorrelatedEq h p := by sorry

end HartSchmeidler.Finite

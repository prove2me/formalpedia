-- Prove2me | Theorems.Thm_HartSchmeidler_Finite_aux_game_correspondence
-- name    : HartSchmeidler.Finite.aux_game_correspondence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:50:54.288373+00:00
-- url     : https://prove2.me/theorems/8ce55550-73dd-4ad8-ad31-862a9abf0db6
-- title:
--   Proof of Theorem 1 — correspondence with the auxiliary game
-- statement:
--   For the finite game described above, a lottery $p$ on pure strategy profiles is a correlated equilibrium exactly when it guarantees player I a nonnegative expected payment against every lottery $y$ over player II's triples $(i,r^i,t^i)$:
--
--   $$
--   p\text{ is a correlated equilibrium}\quad\Longleftrightarrow\quad
--   p\text{ is a lottery and }\sum_{s\in S}\sum_{c}p(s)y(c)A(s,c)\ge0
--   \text{ for every lottery }y.
--   $$
--
--   Here $A(s,c)$ is the auxiliary payment defined above. This equivalence links the incentive inequalities to the minimax step of the proof.
--
--   **Formalization Note** The triples form one finite strategy set for player II; $y$ is one lottery over all triples, not a separate lottery for each player. When there are no players, that set is empty and both sides reduce to the requirement that $p$ is a lottery.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 19, proof of Theorem 1 (‘Consider the following auxiliary’); https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Finite_Game

namespace HartSchmeidler.Finite

open Finset

/-- Proof of Theorem 1, p. 19: condition (1) is precisely the guarantee that
player I's mixed strategy earns a nonnegative payoff against every mixed
strategy of player II in the auxiliary game. -/
theorem aux_game_correspondence {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    (h : ι → (∀ i, S i) → ℝ) (p : (∀ i, S i) → ℝ) :
    IsCorrelatedEq h p ↔ AGT.IsLottery p ∧
      ∀ y : Deviation S → ℝ, AGT.IsLottery y →
        0 ≤ ∑ s, ∑ c, p s * y c * auxPayoff h s c := by sorry

end HartSchmeidler.Finite

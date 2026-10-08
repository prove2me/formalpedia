-- Prove2me | Theorems.Thm_MondererShapley_Participation_theorem_6_1
-- name    : MondererShapley.Participation.theorem_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:16.159562+00:00
-- url     : https://prove2.me/theorems/6e96f37c-bf8a-4152-8f7a-ac7d6e07ed90
-- title:
--   Theorem 6.1 — an efficient ψ is the Shapley value on {v_S} iff the participation game Γ(ψ, c, v) is a potential game
-- statement:
--   Let $N$ be a finite set of players, $\psi$ an efficient solution on $G = \bigcup_{S \in 2^N} G(S)$, $c \in \mathbb R^N$ and $v \in G(N)$, i.e. $v$ is a real function on the coalitions of $N$ with $v(\emptyset) = 0$. Let $\Gamma = \Gamma(\psi, c, v)$ be the participation game, in which each player either stays out and receives $c^i$ or participates and receives $\psi(v_{S})(i)$, $S$ being the set of participants. Then
--
--   $$\psi(v_S)(i) = \varphi_i(v_S)\ \ \text{for every } S \subseteq N \text{ and } i \in S \quad\Longleftrightarrow\quad \Gamma(\psi, c, v) \text{ is a potential game},$$
--
--   where $\varphi(v_S)$ is the Shapley value of the restriction $v_S$ of $v$ to the subsets of $S$.
--
--   This is the local characterisation of the Shapley value in Section 6: the cooperative solution concept is recovered from a strategic property (existence of an exact potential) of a non-cooperative game built from it, for any outside options $c$.
--
--   **Formalization Note** Players form a finite type `ι`; strategies are `Bool` (`true` = participate). A solution is `ψ : Finset ι → (Finset ι → ℝ) → ι → ℝ` with `ψ S v` playing the role of $\psi(v_S)$ (see the definition `Solution`); this admits more solutions than the paper's, all of which are covered. The Shapley value formula is supplied (`shapleyOn`) since the paper does not state it. The hypothesis `v ∅ = 0` is "$v \in G(N)$".
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), Theorem 6.1

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame
import Definitions.Def_MondererShapley_Participation_shapleyOn
import Definitions.Def_MondererShapley_Participation_participationPayoff

namespace MondererShapley.Participation

/-- Theorem 6.1: an efficient solution `ψ` is the Shapley value on `{v_S : S ∈ 2^N}` iff the
participation game `Γ(ψ, c, v)` is a potential game. -/
theorem theorem_6_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : Solution ι)
    (hψ : IsEfficient ψ) (c : ι → ℝ) (v : Finset ι → ℝ) (hv : v ∅ = 0) :
    (∀ S : Finset ι, ∀ i ∈ S, ψ S v i = shapleyOn S v i) ↔
      MondererShapley.ClosedPath.IsPotentialGame (Y := fun _ : ι => Bool) (participationPayoff ψ c v) := by sorry

end MondererShapley.Participation

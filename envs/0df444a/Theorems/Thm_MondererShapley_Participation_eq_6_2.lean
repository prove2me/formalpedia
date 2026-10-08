-- Prove2me | Theorems.Thm_MondererShapley_Participation_eq_6_2
-- name    : MondererShapley.Participation.eq_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:58.361607+00:00
-- url     : https://prove2.me/theorems/31cd2a24-a1ff-4865-aea5-7a30aa70bcae
-- title:
--   (6.2) — Γ(ψ, c, v) is a potential game iff some Q has Q(ε_S) − Q(ε_{S∖{i}}) = ψ(v_{S∪{i}})(i) − cⁱ
-- statement:
--   Let $\psi$ be a solution, $c \in \mathbb R^N$ and $v$ a TU game. For $S \subseteq N$ let $\varepsilon_S$ be the profile in which exactly the members of $S$ choose 1. The participation game $\Gamma(\psi, c, v)$ is a potential game if and only if there exists $Q : Y \to \mathbb R$ such that
--
--   $$Q(\varepsilon_S) - Q(\varepsilon_{S \setminus \{i\}}) = \psi(v_{S \cup \{i\}})(i) - c^i \qquad \text{for every } S \subseteq N \text{ and every } i \in S.$$
--
--   This is the reformulation of the potential property on coalitions used in the proof of Theorem 6.1.
--
--   **Formalization Note** Since $i \in S$, $S \cup \{i\} = S$; the statement keeps the page's $S \cup \{i\}$. $Y = \{0, 1\}^N$ is `ι → Bool`; potential game means an exact potential in the sense of (2.2) with unit weights.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), proof of Theorem 6.1, (6.2)

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame
import Definitions.Def_MondererShapley_Participation_participationPayoff
import Definitions.Def_MondererShapley_Participation_profileOf

namespace MondererShapley.Participation

/-- (6.2): the participation game is a potential game iff there is `Q : Y → ℝ` with
`Q(ε_S) − Q(ε_{S∖{i}}) = ψ(v_{S∪{i}})(i) − cⁱ` for every `S ⊆ N` and every `i ∈ S`. -/
theorem eq_6_2 {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : Solution ι) (c : ι → ℝ)
    (v : Finset ι → ℝ) :
    MondererShapley.ClosedPath.IsPotentialGame (Y := fun _ : ι => Bool) (participationPayoff ψ c v) ↔
      ∃ Q : (ι → Bool) → ℝ, ∀ S : Finset ι, ∀ i ∈ S,
        Q (profileOf S) - Q (profileOf (S \ {i})) = ψ (S ∪ {i}) v i - c i := by sorry

end MondererShapley.Participation

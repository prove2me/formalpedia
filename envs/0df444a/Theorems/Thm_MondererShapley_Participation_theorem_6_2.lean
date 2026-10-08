-- Prove2me | Theorems.Thm_MondererShapley_Participation_theorem_6_2
-- name    : MondererShapley.Participation.theorem_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:05.775487+00:00
-- url     : https://prove2.me/theorems/27e3b1a0-681f-48d6-ac2a-62e945a30679
-- title:
--   Theorem 6.2 — an efficient ψ is the Shapley value on G iff Γ(ψ, c, v) is a potential game for every v ∈ G(N)
-- statement:
--   Let $N$ be a finite set of players, $\psi$ an efficient solution on $G = \bigcup_{S \in 2^N} G(S)$ and $c \in \mathbb R^N$. Then $\psi$ is the Shapley value on $G$, i.e.
--
--   $$\psi(w)(i) = \varphi_i(w) \qquad \text{for every coalition } S,\ \text{every } w \in G(S) \text{ and every } i \in S,$$
--
--   if and only if the participation game $\Gamma(\psi, c, v)$ is a potential game for every $v \in G(N)$.
--
--   This is the global characterisation of the Shapley value in Section 6, a corollary of Theorem 6.1.
--
--   **Formalization Note** A game on $S$ is any `w : Finset ι → ℝ` with `w ∅ = 0`, and $\psi(w)$ for $w \in G(S)$ is `ψ S w` (see the definition `Solution`); a game in $G(N)$ is any `v` with `v ∅ = 0`. The Shapley value is `shapleyOn S w`.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), Theorem 6.2

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame
import Definitions.Def_MondererShapley_Participation_shapleyOn
import Definitions.Def_MondererShapley_Participation_participationPayoff

namespace MondererShapley.Participation

/-- Theorem 6.2: an efficient solution `ψ` is the Shapley value on `G = ∪_{S ∈ 2^N} G(S)` iff
`Γ(ψ, c, v)` is a potential game for every `v ∈ G(N)`. -/
theorem theorem_6_2 {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : Solution ι)
    (hψ : IsEfficient ψ) (c : ι → ℝ) :
    (∀ (S : Finset ι) (w : Finset ι → ℝ), w ∅ = 0 → ∀ i ∈ S, ψ S w i = shapleyOn S w i) ↔
      ∀ v : Finset ι → ℝ, v ∅ = 0 →
        MondererShapley.ClosedPath.IsPotentialGame (Y := fun _ : ι => Bool) (participationPayoff ψ c v) := by sorry

end MondererShapley.Participation

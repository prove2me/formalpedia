-- Prove2me | Theorems.Thm_MondererShapley_Participation_eq_6_1
-- name    : MondererShapley.Participation.eq_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:02.830435+00:00
-- url     : https://prove2.me/theorems/ad4e3258-c804-460c-bea6-b46e720e36ad
-- title:
--   (6.1) — joining changes player i's payoff by ψ(v_{S∪{i}})(i) − cⁱ
-- statement:
--   Let $\psi$ be a solution, $c \in \mathbb R^N$, $v$ a TU game, and $u^i$ the payoffs of the participation game $\Gamma(\psi, c, v)$. For every player $i$ and every profile $\varepsilon \in Y = \{0,1\}^N$, with $S = \{ j \ne i : \varepsilon^j = 1\}$ the other participants,
--
--   $$u^i(\varepsilon^{-i}, 1) - u^i(\varepsilon^{-i}, 0) = \psi(v_{S \cup \{i\}})(i) - c^i.$$
--
--   This identity reduces the potential property of $\Gamma(\psi, c, v)$ to a condition on coalitions; it is the first step of the proof of Theorem 6.1.
--
--   **Formalization Note** $(\varepsilon^{-i}, 1)$ and $(\varepsilon^{-i}, 0)$ are `Function.update ε i true` and `Function.update ε i false`. No hypothesis on $\psi$ or $v$ is needed.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), proof of Theorem 6.1, (6.1)

import Mathlib
import Definitions.Def_MondererShapley_Participation_participationPayoff

namespace MondererShapley.Participation

/-- (6.1): `uⁱ(ε⁻ⁱ, 1) − uⁱ(ε⁻ⁱ, 0) = ψ(v_{S∪{i}})(i) − cⁱ` with `S = {j ≠ i : εʲ = 1}`. -/
theorem eq_6_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : Solution ι) (c : ι → ℝ)
    (v : Finset ι → ℝ) (i : ι) (ε : ι → Bool) :
    participationPayoff ψ c v i (Function.update ε i true) -
        participationPayoff ψ c v i (Function.update ε i false) =
      ψ (Finset.univ.filter (fun j => j ≠ i ∧ ε j = true) ∪ {i}) v i - c i := by sorry

end MondererShapley.Participation

-- Prove2me | Theorems.Thm_MondererShapley_Congestion_sub_potential_indep
-- name    : MondererShapley.Congestion.sub_potential_indep
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:26.093759+00:00
-- url     : https://prove2.me/theorems/cac54b94-7c58-4c86-b584-4303b1f75c3b
-- title:
--   Proof of Theorem 3.2, p. 141 — $u^i - P$ does not depend on the strategy of player $i$
-- statement:
--   Let $\Gamma$ be a game in strategic form with finitely many players, strategy sets $Y^i$, payoffs $u^i$, and let $P$ be a potential for $\Gamma$. Then for every player $i$ and every $a^{-i} \in Y^{-i}$ the expression $u^i(a^{-i}, a^i) - P(a^{-i}, a^i)$ does not depend on $a^i \in Y^i$:
--
--   $$u^i(a^{-i}, a^i) - P(a^{-i}, a^i) = u^i(a^{-i}, b^i) - P(a^{-i}, b^i) \qquad \text{for every } a^i, b^i \in Y^i.$$
--
--   This invariance makes the function $Q^i(a^{-i}) = u^i(a^{-i}, a^i) - P(a^{-i}, a^i)$ of (B.4) well defined, and it is what lets the proof of Theorem 3.2 split each payoff into the potential plus a term the player cannot influence.
--
--   **Formalization Note.** $(a^{-i}, x)$ is `Function.update a i x` for a full profile $a$.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 141 (PDF p. 18), proof of Theorem 3.2, display before (B.4)

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotential

namespace MondererShapley.Congestion

/-- Monderer and Shapley (1996), p. 141 (proof of Theorem 3.2): if `P` is a potential for `Γ`, then by
(2.2) the expression `uⁱ(a⁻ⁱ, aⁱ) − P(a⁻ⁱ, aⁱ)` does not depend on `aⁱ ∈ Yⁱ`:
`uⁱ(a⁻ⁱ, aⁱ) − P(a⁻ⁱ, aⁱ) = uⁱ(a⁻ⁱ, bⁱ) − P(a⁻ⁱ, bⁱ)` for every `aⁱ, bⁱ ∈ Yⁱ`. -/
theorem sub_potential_indep {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}
    (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ) (hP : MondererShapley.ClosedPath.IsPotential u P)
    (i : ι) (a : ∀ k, Y k) (x z : Y i) :
    u i (Function.update a i x) - P (Function.update a i x) =
      u i (Function.update a i z) - P (Function.update a i z) := by sorry

end MondererShapley.Congestion

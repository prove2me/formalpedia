-- Prove2me | Theorems.Thm_MondererShapley_ClosedPath_isPotentialGame_of_closed_paths
-- name    : MondererShapley.ClosedPath.isPotentialGame_of_closed_paths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:54.412632+00:00
-- url     : https://prove2.me/theorems/2883af73-ad21-444b-bae5-c5a86315c678
-- title:
--   Theorem 2.8, proof (2) ⇒ (1): vanishing closed-path sums give a potential
-- statement:
--   Let $\Gamma$ be a strategic-form game with payoff vector $u$. If every finite closed path $\gamma$ satisfies $I(\gamma,u)=0$, then $\Gamma$ admits an exact potential $P$:
--
--   $$\bigl(\forall\gamma\text{ closed},\ I(\gamma,u)=0\bigr)\ \Longrightarrow\ \exists P\;\operatorname{IsPotential}(u,P).$$
--
--   This is the converse to the telescoping implication in Theorem 2.8 and turns path independence into a game-wide function.
--
--   **Formalization Note** The empty profile space is permitted; in that case a potential exists as a function on the empty type. Players are finite, but their strategy sets need not be finite.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 138 (PDF p. 15), Theorem 2.8, proof (2) ⇒ (1); https://doi.org/10.1006/game.1996.0044

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame
import Definitions.Def_MondererShapley_ClosedPath_FinPath

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Theorem 2.8, proof of (2) implies (1), p. 138. -/
theorem isPotentialGame_of_closed_paths [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ)
    (hclosed : ∀ γ : FinPath Y, γ.IsClosed → γ.I u = 0) :
    IsPotentialGame u := by sorry

end MondererShapley.ClosedPath

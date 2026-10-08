-- Prove2me | Theorems.Thm_MondererShapley_ClosedPath_closed_paths_of_four
-- name    : MondererShapley.ClosedPath.closed_paths_of_four
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:50.08021+00:00
-- url     : https://prove2.me/theorems/762c622b-0ade-4fd7-8d58-b476143e05d4
-- title:
--   Theorem 2.8, proof (4) ⇒ (2): four-cycles control all closed paths
-- statement:
--   Let $u$ be the payoff vector of a game with finitely many players. If $I(\gamma,u)=0$ for every simple closed path $\gamma$ of length four, then
--
--   $$I(\mu,u)=0\qquad\text{for every finite closed path }\mu.$$
--
--   This is the substantial implication of Theorem 2.8: checking the elementary four-corner cycles suffices for all closed paths.
--
--   **Formalization Note** Length counts genuine one-player steps. The hypothesis is restricted to simple closed four-step paths, not all four-step walks.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), pp. 138–139 (PDF pp. 15–16), Theorem 2.8, proof (4) ⇒ (2); https://doi.org/10.1006/game.1996.0044

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_FinPath

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Theorem 2.8, proof of (4) implies (2), pp. 138--139. -/
theorem closed_paths_of_four [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ)
    (hfour : ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.len = 4 → γ.I u = 0) :
    ∀ γ : FinPath Y, γ.IsClosed → γ.I u = 0 := by sorry

end MondererShapley.ClosedPath

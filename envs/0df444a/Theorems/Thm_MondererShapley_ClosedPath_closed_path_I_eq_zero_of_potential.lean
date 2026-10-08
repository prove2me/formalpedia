-- Prove2me | Theorems.Thm_MondererShapley_ClosedPath_closed_path_I_eq_zero_of_potential
-- name    : MondererShapley.ClosedPath.closed_path_I_eq_zero_of_potential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:12.067934+00:00
-- url     : https://prove2.me/theorems/1cb9a991-94b6-4ed5-ae29-96e2da573138
-- title:
--   Theorem 2.8, proof (1) ⇒ (2): a potential has zero closed-path sum
-- statement:
--   Suppose $P$ is an exact potential for a game $\Gamma$ with payoff vector $u$. For every finite closed path $\gamma$,
--
--   $$I(\gamma,u)=0.$$
--
--   Along each step, the deviator's payoff change equals the change in $P$, so the path sum records only the difference between the terminal and initial potential values. This is the forward implication in Theorem 2.8.
--
--   **Formalization Note** Players form a finite type, strategy sets are arbitrary, and every path step changes exactly one coordinate to a different value.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 138 (PDF p. 15), Theorem 2.8, proof (1) ⇒ (2); https://doi.org/10.1006/game.1996.0044

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotential
import Definitions.Def_MondererShapley_ClosedPath_FinPath

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Theorem 2.8, proof of (1) implies (2), p. 138. -/
theorem closed_path_I_eq_zero_of_potential [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ)
    (hP : IsPotential u P) (γ : FinPath Y) (hγ : γ.IsClosed) : γ.I u = 0 := by sorry

end MondererShapley.ClosedPath

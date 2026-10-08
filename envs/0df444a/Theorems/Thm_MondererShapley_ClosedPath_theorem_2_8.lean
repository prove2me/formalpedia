-- Prove2me | Theorems.Thm_MondererShapley_ClosedPath_theorem_2_8
-- name    : MondererShapley.ClosedPath.theorem_2_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:16.875405+00:00
-- url     : https://prove2.me/theorems/24d30353-c008-4fb0-af3d-08ba1a6f3b42
-- title:
--   Theorem 2.8: exact potentials and closed paths of length four
-- statement:
--   For a strategic-form game $\Gamma$ with finitely many players, the following four claims are equivalent:
--
--   1. $\Gamma$ admits an exact potential.
--   2. $I(\gamma,u)=0$ for every finite closed path $\gamma$.
--   3. $I(\gamma,u)=0$ for every finite simple closed path $\gamma$.
--   4. $I(\gamma,u)=0$ for every finite simple closed path $\gamma$ of length four.
--
--   In symbols, the final criterion uses
--
--   $$I(\gamma,u)=\sum_{k=1}^{N}\bigl(u^{i_k}(y_k)-u^{i_k}(y_{k-1})\bigr)=0$$
--
--   on every simple closed $\gamma=(y_0,\ldots,y_N)$ with $N=4$. This characterization reduces the global potential property to a local condition on four-corner cycles.
--
--   **Formalization Note** The statement retains all four equivalence clauses. Players form a finite type; their strategy sets are arbitrary. A step changes exactly one coordinate to a different value, a simple closed path repeats no vertex before its terminal return, and its length is its number of steps.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 131 (PDF p. 8), Theorem 2.8; https://doi.org/10.1006/game.1996.0044

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame
import Definitions.Def_MondererShapley_ClosedPath_FinPath

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- The four equivalent conditions of Theorem 2.8, p. 131. -/
theorem theorem_2_8 [Fintype ι] (u : ι → (∀ i, Y i) → ℝ) :
    [IsPotentialGame u,
     ∀ γ : FinPath Y, γ.IsClosed → γ.I u = 0,
     ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.I u = 0,
     ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.len = 4 → γ.I u = 0].TFAE := by sorry

end MondererShapley.ClosedPath

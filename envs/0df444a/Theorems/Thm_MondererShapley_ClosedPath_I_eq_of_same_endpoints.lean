-- Prove2me | Theorems.Thm_MondererShapley_ClosedPath_I_eq_of_same_endpoints
-- name    : MondererShapley.ClosedPath.I_eq_of_same_endpoints
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:02.764987+00:00
-- url     : https://prove2.me/theorems/51a7b1b6-85bc-4581-ac28-82db4c9b4fb6
-- title:
--   Theorem 2.8, path-independence claim (A.1)
-- statement:
--   Assume $I(\mu,u)=0$ for every finite closed path $\mu$. If two finite paths $\gamma_1$ and $\gamma_2$ have the same initial vertex and the same terminal vertex, then
--
--   $$I(\gamma_1,u)=I(\gamma_2,u).$$
--
--   The path sum therefore depends only on its endpoints, making the potential constructed in equation (A.1) well defined.
--
--   **Formalization Note** The paths carry their unique deviators explicitly, and no finiteness condition is placed on players' strategy sets.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 138 (PDF p. 15), Theorem 2.8, proof (2) ⇒ (1), claim preceding (A.1); https://doi.org/10.1006/game.1996.0044

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_FinPath

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Theorem 2.8, proof of (2) implies (1), path-independence claim (A.1), p. 138. -/
theorem I_eq_of_same_endpoints [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ)
    (hclosed : ∀ γ : FinPath Y, γ.IsClosed → γ.I u = 0)
    (γ₁ γ₂ : FinPath Y)
    (hstart : γ₁.pt 0 = γ₂.pt 0)
    (hend : γ₁.pt (Fin.last γ₁.len) = γ₂.pt (Fin.last γ₂.len)) :
    γ₁.I u = γ₂.I u := by sorry

end MondererShapley.ClosedPath

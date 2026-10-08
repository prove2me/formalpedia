-- Prove2me | Theorems.Thm_MondererShapley_ClosedPath_swap_two_steps
-- name    : MondererShapley.ClosedPath.swap_two_steps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:08.588988+00:00
-- url     : https://prove2.me/theorems/5ede3d37-469b-4134-959f-eb0ce0da3dfb
-- title:
--   Theorem 2.8, exchange of two consecutive deviations (A.2)
-- statement:
--   Suppose $I(\gamma,u)=0$ for every simple closed path of length four. Let $a\to b$ be a genuine deviation by player $i$ and $b\to c$ one by a different player $k$. Set $z$ to the profile obtained from $a$ by giving player $k$ the strategy held at $c$. Then $a\to z$ is a step by $k$, $z\to c$ is a step by $i$, and
--
--   $$\bigl(u^i(b)-u^i(a)\bigr)+\bigl(u^k(c)-u^k(b)\bigr)=\bigl(u^k(z)-u^k(a)\bigr)+\bigl(u^i(c)-u^i(z)\bigr).$$
--
--   Thus the two routes around the same four-corner cycle have the same path sum. This is the local exchange used in equation (A.2).
--
--   **Formalization Note** The page calls the second deviator player 1; the statement renames it $k$. Distinct deviators and genuine steps ensure the four vertices form a simple cycle.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 139 (PDF p. 16), Theorem 2.8, proof (4) ⇒ (2), Eq. (A.2); https://doi.org/10.1006/game.1996.0044

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_FinPath

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Theorem 2.8, proof of (4) implies (2), local exchange in (A.2), p. 139. -/
theorem swap_two_steps [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ)
    (hfour : ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.len = 4 → γ.I u = 0)
    (a b c : ∀ i, Y i) (i k : ι) (hik : i ≠ k)
    (hab : IsStep a b i) (hbc : IsStep b c k) :
    let z := Function.update a k (c k)
    IsStep a z k ∧ IsStep z c i ∧
      (u i b - u i a) + (u k c - u k b) =
        (u k z - u k a) + (u i c - u i z) := by sorry

end MondererShapley.ClosedPath

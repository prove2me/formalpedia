-- Prove2me | Theorems.Thm_KellyReversibility_Allocation_lagrangian_minimizer
-- name    : KellyReversibility.Allocation.lagrangian_minimizer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:08:13.158894+00:00
-- url     : https://prove2.me/theorems/74078167-a525-456a-9d2d-7d25e7e3244c
-- title:
--   Proof of Theorem 4.1, p. 97 — the Lagrangian is minimized at φ_j = a_j + √(a_j/(y f_j))
-- statement:
--   Let $a_j > 0$ and $f_j > 0$ for $j = 1, \dots, J$, let $F \in \mathbb{R}$ and let $y > 0$ be a Lagrange multiplier. Over capacity vectors with $\phi_j > a_j$ for all $j$, the Lagrangian
--   $$L(\phi) = \sum_j \frac{a_j}{\phi_j - a_j} + y\Big(\sum_j f_j\phi_j - F\Big)$$
--   is minimized by the choice
--   $$\phi^y_j = a_j + \sqrt{\frac{a_j}{y f_j}},$$
--   which satisfies $\phi^y_j > a_j$, and every other vector $\phi$ with $\phi_j > a_j$ for all $j$ has $L(\phi) > L(\phi^y)$.
--
--   This is the unconstrained step of the Lagrangian method used to prove Theorem 4.1.
--
--   **Formalization Note** The book says "$L$ is minimized by the choice"; the strict inequality for every other point (uniqueness of the minimizer) is a slight strengthening, true because $L$ is strictly convex on the region $\phi_j > a_j$. The minimization is over the open region $\phi_j > a_j$, where every term of $L$ is finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 97, proof of Theorem 4.1 (the Lagrangian L and the choice φ_j = a_j + √(a_j/(y f_j)))

import Mathlib
import Definitions.Def_KellyReversibility_Allocation_CapacityAllocation

namespace KellyReversibility.Allocation

theorem lagrangian_minimizer {J : ℕ} (a f : Fin J → ℝ) (F y : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hy : 0 < y) :
    let φstar : Fin J → ℝ := fun j => a j + Real.sqrt (a j / (y * f j))
    (∀ j, a j < φstar j) ∧
      ∀ φ : Fin J → ℝ, (∀ j, a j < φ j) → φ ≠ φstar →
        lagrangian a f F y φstar < lagrangian a f F y φ := by sorry

end KellyReversibility.Allocation

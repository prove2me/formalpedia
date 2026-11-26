-- Prove2me | Theorems.Thm_LefebvreVariations_no_exotic_smooth_sphere_five_six
-- name    : LefebvreVariations.no_exotic_smooth_sphere_five_six
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:33:47.164985+00:00
-- url     : https://prove2.me/theorems/887ed393-9e7f-4c03-9b6c-d57731ebf456
-- title:
--   Lefebvre's variations, No. 217 — on a theme by Kervaire and Milnor: a smooth manifold homeomorphic to the n-sphere is diffeomorphic to it for n equal to 5 or 6
-- statement:
--   Let $n\in\{5,6\}$ and let $M$ be a smooth ($C^\infty$) $n$-manifold which is homeomorphic to the unit sphere $S^n\subset\mathbb{R}^{n+1}$. Then
--   $$M\;\cong_{C^\infty}\;S^n.$$
--
--   By Kervaire and Milnor the group $\Theta_n$ of oriented diffeomorphism classes of homotopy $n$-spheres is trivial for $n=5$ and $n=6$ (for comparison, $|\Theta_7|=28$ is where the first exotic sphere appears). The neighbouring dimension $n=4$ is the open smooth Poincaré problem.
--
--   **Formalization Note** Same formalization as `SmoothPoincare4.no_exotic_smooth_four_sphere` with the dimension `n` a variable restricted to `5` or `6`: `M : Type` is an `n`-dimensional `C^∞` manifold (`ChartedSpace (EuclideanSpace ℝ (Fin n)) M`, `IsManifold (𝓡 n) ∞ M`), homeomorphic to `sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`, and the conclusion is a `C^∞` diffeomorphism onto that sphere (`M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere …`). Orientation is not required: composing with a reflection removes the distinction between `Θ_n` and unoriented classes.
--
--   **Why this is a variation.** Known neighbours of the open problem SmoothPoincare4.no_exotic_smooth_four_sphere (open on the platform): Kervaire and Milnor showed that the group of homotopy spheres is trivial in dimensions 5 and 6, so no exotic sphere exists there. The formalization copies the style of the parent with n a variable; it is not a formal special case of the n = 4 statement.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): the smooth Poincare problem in dimension 4, SmoothPoincare4.no_exotic_smooth_four_sphere (open on the platform); this statement is the known answer in the dimensions 5 and 6 just above it, in the same formalization style (not a formal special case).
--   Source: M. Kervaire and J. Milnor, 'Groups of homotopy spheres: I', Ann. of Math. 77 (1963), 504-537 (the table of Theta_n for n <= 18, cited from memory); S. Smale, 'Generalized Poincare's conjecture in dimensions greater than four', Ann. of Math. 74 (1961) (cited from memory) for the reduction of smooth structures to homotopy spheres.

import Mathlib

set_option autoImplicit false

open scoped Manifold ContDiff
open Metric

namespace LefebvreVariations

/-- Kervaire–Milnor: the groups of homotopy spheres `Θ₅` and `Θ₆` are trivial, so a smooth manifold
homeomorphic to `S⁵` or `S⁶` is diffeomorphic to it (the dimensions just above the open case
`n = 4`). -/
theorem no_exotic_smooth_sphere_five_six (n : ℕ) (hn : n = 5 ∨ n = 6) (M : Type)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (h : Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Nonempty (M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  sorry

end LefebvreVariations

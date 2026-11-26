-- Prove2me | Theorems.Thm_LefebvreVariations_exotic_smooth_sphere_dim_eight_to_eleven
-- name    : LefebvreVariations.exotic_smooth_sphere_dim_eight_to_eleven
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:34:01.448861+00:00
-- url     : https://prove2.me/theorems/60cde71e-a807-47b0-8728-ef51a0354c4a
-- title:
--   Lefebvre's variations, No. 180 — on a theme by Kervaire and Milnor: there is an exotic smooth n-sphere for each n from 8 to 11
-- statement:
--   For every integer $n$ with $8\le n\le 11$ there is a smooth ($C^\infty$) $n$-manifold $M$ which is homeomorphic to the sphere $S^n\subset\mathbb{R}^{n+1}$ but not diffeomorphic to it:
--   $$\exists M,\quad M\approx S^n\quad\text{and}\quad M\not\cong_{C^\infty}S^n .$$
--
--   By Kervaire and Milnor the groups of homotopy spheres have orders $|\Theta_8|=2$, $|\Theta_9|=8$, $|\Theta_{10}|=6$ and $|\Theta_{11}|=992$, all non-trivial. Milnor's exotic $7$-sphere (the first one ever found, with $|\Theta_7|=28$) is the case $n=7$ and the case $n=4$ is open.
--
--   **Formalization Note** Same formalization as `SmoothPoincare4.milnor_exotic_seven_sphere`, with the dimension `n` a variable in the range `8 ≤ n ≤ 11`: the witness is a `Type M` with a topology, an `n`-dimensional charted space structure over `EuclideanSpace ℝ (Fin n)` and `IsManifold (𝓡 n) ∞ M`, such that `M` is homeomorphic to `sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1` while there is no `C^∞` diffeomorphism `M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere …`.
--
--   **Why this is a variation.** Next dimensions after Milnor's exotic 7-sphere (SmoothPoincare4.milnor_exotic_seven_sphere, open on the platform): exotic smooth spheres exist in every dimension from 8 to 11 by Kervaire and Milnor's computation of the groups of homotopy spheres (orders 2, 8, 6, 992 in dimensions 8 to 11). The statement copies the formalization of the parent with n a variable in 8..11.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): Milnor's exotic 7-sphere, SmoothPoincare4.milnor_exotic_seven_sphere (open on the platform); this statement is the next dimensions 8 to 11, in the same formalization style with n a variable.
--   Source: M. Kervaire and J. Milnor, 'Groups of homotopy spheres: I', Ann. of Math. 77 (1963), 504-537, table of the orders of Theta_n (orders |Theta_7|=28, |Theta_8|=2, |Theta_9|=8, |Theta_10|=6, |Theta_11|=992 checked against the table of the paper via web search). J. Milnor, 'On manifolds homeomorphic to the 7-sphere', Ann. of Math. 64 (1956) for the dimension 7.

import Mathlib

set_option autoImplicit false

open scoped Manifold ContDiff
open Metric

namespace LefebvreVariations

/-- Kervaire–Milnor: `Θ₈ ≅ ℤ/2`, `Θ₉ ≅ (ℤ/2)³`, `Θ₁₀ ≅ ℤ/6`, `Θ₁₁ ≅ ℤ/992`, so each of the dimensions
`8, 9, 10, 11` carries an exotic smooth sphere. The dimension `7` is
`SmoothPoincare4.milnor_exotic_seven_sphere`. -/
theorem exotic_smooth_sphere_dim_eight_to_eleven (n : ℕ) (h8 : 8 ≤ n) (h11 : n ≤ 11) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
      (_ : IsManifold (𝓡 n) ∞ M),
      Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ∧
      IsEmpty (M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  sorry

end LefebvreVariations

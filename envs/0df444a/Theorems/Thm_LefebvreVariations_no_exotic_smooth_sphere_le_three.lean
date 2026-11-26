-- Prove2me | Theorems.Thm_LefebvreVariations_no_exotic_smooth_sphere_le_three
-- name    : LefebvreVariations.no_exotic_smooth_sphere_le_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:33:26.920571+00:00
-- url     : https://prove2.me/theorems/3b282f6e-b4b9-5aed-8318-0ba021dcb8b3
-- title:
--   Lefebvre's variations, No. 215 — on a theme by Kervaire and Milnor: a smooth manifold homeomorphic to the n-sphere is diffeomorphic to it for n at most 3
-- statement:
--   Let $n\in\{0,1,2,3\}$ and let $M$ be a smooth ($C^\infty$) $n$-manifold which is homeomorphic to the unit sphere $S^n\subset\mathbb{R}^{n+1}$. Then
--   $$M\;\cong_{C^\infty}\;S^n,$$
--   that is, $M$ is diffeomorphic to the standard smooth sphere.
--
--   In dimensions $n\le 3$ there are no exotic spheres: every smooth structure on a topological $n$-sphere is the standard one. The case $n=4$ (does $S^4$ carry an exotic smooth structure?) is the famous open problem, and the case $n=7$ is where Milnor found the first exotic sphere.
--
--   **Formalization Note** `M : Type` with `[TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]`; the hypothesis is `Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)` and the conclusion is the existence of a `C^∞` diffeomorphism `M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere …` (Mathlib's smooth structure on the sphere). The hypothesis `n ≤ 3` includes `n = 0` (two points, trivially true). No Hausdorff or second-countability hypothesis is needed since `M` is homeomorphic to a sphere.
--
--   **Why this is a variation.** Known cases of the open smooth Poincare problem in dimension 4 (SmoothPoincare4.no_exotic_smooth_four_sphere, open on the platform): no exotic smooth n-sphere exists for n at most 3. It is stated in the same Mathlib formalization as the parent, with n a variable, but it is not a formal special case of the n = 4 statement.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): the smooth Poincare problem in dimension 4, SmoothPoincare4.no_exotic_smooth_four_sphere (open on the platform, same formalization style); this statement collects the dimensions n <= 3 below it, where the answer is known (no exotic sphere).
--   Source: n = 1, 2: classical (classification of 1-manifolds; S. Smale, 'Diffeomorphisms of the 2-sphere', Proc. AMS 10 (1959), cited from memory). n = 3: E. Moise, 'Affine structures in 3-manifolds', Ann. of Math. 56 (1952) and J. Munkres, 'Obstructions to the smoothing of piecewise-differentiable homeomorphisms', Ann. of Math. 72 (1960) (both cited from memory, titles and journals not verified). n = 0 is trivial.

import Mathlib

set_option autoImplicit false

open scoped Manifold ContDiff
open Metric

namespace LefebvreVariations

/-- For `n ≤ 3` a smooth `n`-manifold homeomorphic to the sphere `S^n` is diffeomorphic to it: the
dimensions below the open case `n = 4` of `SmoothPoincare4.no_exotic_smooth_four_sphere`. -/
theorem no_exotic_smooth_sphere_le_three (n : ℕ) (hn : n ≤ 3) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (h : Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Nonempty (M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  sorry

end LefebvreVariations

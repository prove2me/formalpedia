-- Prove2me | Theorems.Thm_LefebvreVariations_unique_smooth_structure_euclidean_of_ne_four
-- name    : LefebvreVariations.unique_smooth_structure_euclidean_of_ne_four
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:34:18.871558+00:00
-- url     : https://prove2.me/theorems/255b262d-a48d-4620-b6ff-f95da79846bd
-- title:
--   Lefebvre's variations, No. 219 — on a theme by Freedman and Donaldson: every smooth manifold homeomorphic to Euclidean n-space is diffeomorphic to it when n is not 4
-- statement:
--   Let $n\neq 4$ and let $M$ be a smooth ($C^\infty$) $n$-manifold which is homeomorphic to Euclidean space $\mathbb{R}^n$. Then
--   $$M\;\cong_{C^\infty}\;\mathbb{R}^n .$$
--
--   So $\mathbb{R}^n$ has exactly one smooth structure up to diffeomorphism in every dimension except $4$, where it has a continuum of them. The cases $n\le 3$ go back to Moise and Munkres, and for $n\ge 5$ it follows from Stallings' theorem on PL structures together with smoothing theory (Hirsch, Mazur, Munkres).
--
--   **Formalization Note** Same formalization style as `SmoothPoincare4.continuum_exotic_R4`: `M : Type` carries `[TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]`, the hypothesis is `Nonempty (M ≃ₜ EuclideanSpace ℝ (Fin n))` and the conclusion `Nonempty (M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ EuclideanSpace ℝ (Fin n))`, with `EuclideanSpace ℝ (Fin n)` carrying its standard smooth structure. The hypothesis `n ≠ 4` includes `n = 0` (a point).
--
--   **Why this is a variation.** Complement of the open problem SmoothPoincare4.continuum_exotic_R4 (open on the platform, a continuum of exotic smooth structures on R^4): in every dimension other than 4 the smooth structure on Euclidean space is unique (Moise and Munkres for n at most 3, Stallings with smoothing theory for n at least 5). Same formalization style as the parent, with n a variable; not a formal special case of it.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): exotic smooth structures on R^4, SmoothPoincare4.continuum_exotic_R4 (open on the platform); this statement is the complementary known case: in every dimension n different from 4 the smooth structure on R^n is unique.
--   Source: J. Stallings, "The piecewise-linear structure of Euclidean space", Proc. Cambridge Philos. Soc. 58 (1962), 481-488 (PL uniqueness for n >= 5, cited from memory), combined with smoothing theory (Hirsch-Mazur, Munkres; cited from memory) to pass from PL to smooth; E. Moise (1952) and J. Munkres, Ann. of Math. 72 (1960) for n <= 3 (cited from memory); n = 0 is trivial. Uncountably many structures on R^4: Taubes 1987 (cited from memory).

import Mathlib

set_option autoImplicit false

open scoped Manifold ContDiff

namespace LefebvreVariations

/-- Outside dimension `4`, `ℝⁿ` has a unique smooth structure: a smooth manifold homeomorphic to
`ℝⁿ` is diffeomorphic to it. In dimension `4` there are uncountably many
(`SmoothPoincare4.continuum_exotic_R4`). -/
theorem unique_smooth_structure_euclidean_of_ne_four (n : ℕ) (hn : n ≠ 4) (M : Type)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (h : Nonempty (M ≃ₜ EuclideanSpace ℝ (Fin n))) :
    Nonempty (M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ EuclideanSpace ℝ (Fin n)) := by
  sorry

end LefebvreVariations

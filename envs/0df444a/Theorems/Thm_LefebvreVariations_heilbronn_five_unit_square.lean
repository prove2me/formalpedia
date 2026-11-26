-- Prove2me | Theorems.Thm_LefebvreVariations_heilbronn_five_unit_square
-- name    : LefebvreVariations.heilbronn_five_unit_square
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:51:21.312509+00:00
-- url     : https://prove2.me/theorems/d13e5be4-0aca-561a-9ae8-e2d788dc4430
-- title:
--   Lefebvre's variations, No. 108 — on a theme by Heilbronn: the Heilbronn number of five points in the unit square
-- statement:
--   Let $H_5$ be the largest $\alpha$ such that some five points of the unit square $[0,1]^2$ span only triangles of area at least $\alpha$. Then
--   $$
--   H_5=\frac{\sqrt3}{9}.
--   $$
--   That is: every five points of $[0,1]^2$ contain three whose triangle has area at most $\sqrt3/9$, and there are five points of $[0,1]^2$ all of whose triangles have area at least $\sqrt3/9$.
--
--   This is the Heilbronn triangle problem at its first non-trivial size. The asymptotic behaviour of the Heilbronn numbers $H_n$ (between $\Omega(\log n/n^2)$ and $O(n^{-8/7+o(1)})$) is open; exact values are known only for a few small $n$.
--
--   **Formalization Note** Points are `p : Fin 5 → ℝ × ℝ` with every `p i ∈ Set.Icc 0 1 ×ˢ Set.Icc 0 1`. The area of the triple `i < j < k` is `|(xⱼ−xᵢ)(yₖ−yᵢ) − (xₖ−xᵢ)(yⱼ−yᵢ)| / 2`. The statement is a conjunction: (1) every such `p` has indices `i < j < k` with area `≤ √3/9`; (2) there is such a `p` all of whose triples have area `≥ √3/9`. Coincident points are allowed in (1) (they give area `0`).
--
--   **Why this is a variation.** Variation of the Heilbronn triangle problem. The platform entry heilbronn_triangle_problem is an asymptotic statement marked Disproved (as formalized), so there is no open platform parent; this statement is the exact finite value of the Heilbronn number for n = 5 points in the unit square, known to be sqrt(3)/9. The asymptotic order of the Heilbronn numbers remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): Heilbronn's triangle problem; the platform entry heilbronn_triangle_problem is marked Disproved (as formalized), not an open parent. This is the exact value for n = 5 in the unit square.
--   Source (verified by search): L. Yang, J. Zhang and Z. Zeng, 'Heilbronn problem for five points', ICTP technical report IC/91/252 (1991), which proves H_5 = sqrt(3)/9. Numerical check done here: random-restart hill climbing over five points reached 0.19240 against sqrt(3)/9 = 0.19245, never above.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The Heilbronn number of five points in the unit square is √3/9: every five points of the
unit square span a triangle of area at most √3/9, and some five points span only triangles of
area at least √3/9. -/
theorem heilbronn_five_unit_square :
    (∀ p : Fin 5 → ℝ × ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
      ∃ i j k : Fin 5, i < j ∧ j < k ∧
        |((p j).1 - (p i).1) * ((p k).2 - (p i).2) - ((p k).1 - (p i).1) * ((p j).2 - (p i).2)| / 2
          ≤ Real.sqrt 3 / 9) ∧
    (∃ p : Fin 5 → ℝ × ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ∀ i j k : Fin 5, i < j → j < k →
        Real.sqrt 3 / 9 ≤
          |((p j).1 - (p i).1) * ((p k).2 - (p i).2) - ((p k).1 - (p i).1) * ((p j).2 - (p i).2)| / 2) := by
  sorry

end LefebvreVariations

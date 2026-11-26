-- Prove2me | Theorems.Thm_LefebvreVariations_heilbronn_six_unit_square
-- name    : LefebvreVariations.heilbronn_six_unit_square
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:51:38.217268+00:00
-- url     : https://prove2.me/theorems/08ecb3e6-38a1-5eca-893d-1418f5f6a46d
-- title:
--   Lefebvre's variations, No. 109 — on a theme by Heilbronn: the Heilbronn number of six points in the unit square
-- statement:
--   Let $H_6$ be the largest $\alpha$ such that some six points of the unit square $[0,1]^2$ span only triangles of area at least $\alpha$. Then
--   $$
--   H_6=\frac18.
--   $$
--   That is: every six points of $[0,1]^2$ contain three whose triangle has area at most $1/8$, and there are six points of $[0,1]^2$ all of whose triangles have area at least $1/8$.
--
--   This is the Heilbronn triangle problem for six points. The asymptotic behaviour of the Heilbronn numbers $H_n$ is open; exact values are known only for a few small $n$.
--
--   **Formalization Note** Points are `p : Fin 6 → ℝ × ℝ` with every `p i ∈ Set.Icc 0 1 ×ˢ Set.Icc 0 1`. The area of the triple `i < j < k` is `|(xⱼ−xᵢ)(yₖ−yᵢ) − (xₖ−xᵢ)(yⱼ−yᵢ)| / 2`. The statement is a conjunction: (1) every such `p` has indices `i < j < k` with area `≤ 1/8`; (2) there is such a `p` all of whose triples have area `≥ 1/8`. Coincident points are allowed in (1) (they give area `0`).
--
--   **Why this is a variation.** Variation of the Heilbronn triangle problem. The platform entry heilbronn_triangle_problem is an asymptotic statement marked Disproved (as formalized), so there is no open platform parent; this statement is the exact finite value of the Heilbronn number for n = 6 points in the unit square, known to be 1/8. The asymptotic order of the Heilbronn numbers remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): Heilbronn's triangle problem; the platform entry heilbronn_triangle_problem is marked Disproved (as formalized), not an open parent. This is the exact value for n = 6 in the unit square.
--   Source (verified by search): A. Dress, L. Yang and Z. Zeng, 'Heilbronn problem for six points in a planar convex body', in Minimax and Applications, 1995 (Springer/Kluwer; pages not verified), which proves H_6 = 1/8. Numerical check done here: hill climbing over six points reached 0.124974 against 1/8, never above.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The Heilbronn number of six points in the unit square is 1/8: every six points of the unit
square span a triangle of area at most 1/8, and some six points span only triangles of area at
least 1/8. -/
theorem heilbronn_six_unit_square :
    (∀ p : Fin 6 → ℝ × ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
      ∃ i j k : Fin 6, i < j ∧ j < k ∧
        |((p j).1 - (p i).1) * ((p k).2 - (p i).2) - ((p k).1 - (p i).1) * ((p j).2 - (p i).2)| / 2
          ≤ 1 / 8) ∧
    (∃ p : Fin 6 → ℝ × ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ∀ i j k : Fin 6, i < j → j < k →
        1 / 8 ≤
          |((p j).1 - (p i).1) * ((p k).2 - (p i).2) - ((p k).1 - (p i).1) * ((p j).2 - (p i).2)| / 2) := by
  sorry

end LefebvreVariations

-- Prove2me | Theorems.Thm_LefebvreVariations_perfect_cuboid_of_le_200
-- name    : LefebvreVariations.perfect_cuboid_of_le_200
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:04:09.604814+00:00
-- url     : https://prove2.me/theorems/87b7b9e7-af06-43d2-90fc-74dbf1911ee2
-- title:
--   Lefebvre's variations, No. 47 — on a theme by Euler: there is no perfect cuboid with all edges at most 200
-- statement:
--   There are no positive integers $a,b,c\le 200$ and $d_{ab},d_{ac},d_{bc},d_{abc}$ with
--   $$a^2+b^2=d_{ab}^2,\quad a^2+c^2=d_{ac}^2,\quad b^2+c^2=d_{bc}^2,\quad a^2+b^2+c^2=d_{abc}^2 .$$
--
--   In words: no integer box with all edges at most $200$ has integer face diagonals and an integer space diagonal. Euler bricks (the first three equations alone) exist, the smallest being $(44,117,240)$, but its longest edge exceeds $200$; the finite statement here is therefore a statement about boxes below that size, and a perfect cuboid is not known to exist at any size.
--
--   **Formalization Note** This is the parent `perfect_cuboid_problem` with the three extra conjuncts `a ≤ 200 ∧ b ≤ 200 ∧ c ≤ 200` inside the existential; the equations are over `ℕ` with squares, so no subtraction or division is involved.
--
--   **Why this is a variation.** This is a variation of the open platform problem perfect_cuboid_problem (existence of a perfect cuboid). It is the problem played at an explicit finite size, all edges at most 200, in the parent's own formulation. It is a partial result: the box-bounded search every computational and structural approach is measured against, and a proof by exhaustion gives a ready finite template for larger bounds.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The perfect cuboid problem is classical; the smallest Euler brick (44, 117, 240) is due to Paul Halcke (1719) (cited from memory, not re-checked). No perfect cuboid is known and extensive computer searches have found none (Matson, 2017, and others; cited from memory, not re-checked). The range all edges <= 200 was checked directly in Python for this statement. It is the platform theorem perfect_cuboid_problem with edges bounded by 200.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem perfect_cuboid_of_le_200 :
    ¬ ∃ (a b c : ℕ), 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a ≤ 200 ∧ b ≤ 200 ∧ c ≤ 200 ∧
      ∃ (dab dac dbc dabc : ℕ),
        a ^ 2 + b ^ 2 = dab ^ 2 ∧
        a ^ 2 + c ^ 2 = dac ^ 2 ∧
        b ^ 2 + c ^ 2 = dbc ^ 2 ∧
        a ^ 2 + b ^ 2 + c ^ 2 = dabc ^ 2 := by sorry
end LefebvreVariations

-- Prove2me | Theorems.Thm_Hairer_grid_overlap_count
-- name    : Hairer.grid_overlap_count
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T20:05:05.446768+00:00
-- url     : https://prove2.me/theorems/219bc61b-19fd-40a0-994e-588ee6d74928
-- title:
--   Uniform bound on the number of overlapping grid boxes
-- statement:
--   Fix a centre $x\in\mathbb R^d$, fine widths $a_i$, and positive coarse widths $c_i$ with $a_i\le c_i$. There is a finite set $S\subset\mathbb Z^d$, of cardinality at most $5^d$, containing every coarse index $k$ whose box meets the fine box:
--   $$\bigl(\exists y:\ |y_i-x_i|<a_i\ \text{and}\ |y_i/c_i-k_i|<1\ \text{for every }i\bigr)\ \Longrightarrow\ k\in S.$$
--   The bound is independent of the centre and widths. In a smooth grid construction of reconstruction, this controls the number of coarse cells contributing to each fine cell.
-- source:
--   Elementary coordinate-box counting estimate used in the smooth partition approach to reconstruction.

import Definitions.Def_Hairer_TestFunctions

set_option autoImplicit false
noncomputable section

namespace Hairer

theorem grid_overlap_count {d : ℕ} (x : Pt d) (a c : Fin d → ℝ)
    (hc : ∀ i, 0 < c i) (hac : ∀ i, a i ≤ c i) :
    ∃ S : Finset (Fin d → ℤ), S.card ≤ 5 ^ d ∧
      ∀ k : Fin d → ℤ, (∃ y : Pt d, (∀ i, |y i - x i| < a i) ∧
        (∀ i, |y i / c i - (k i : ℝ)| < 1)) → k ∈ S := by sorry

end Hairer

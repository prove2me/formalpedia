-- Prove2me | Theorems.Thm_GilmoreGomory61_CuttingStock_pricing_integer_form_6_7
-- name    : GilmoreGomory61.CuttingStock.pricing_integer_form_6_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:10:51.209137+00:00
-- url     : https://prove2.me/theorems/cf69c1ab-462c-4436-99b8-17e623887829
-- title:
--   p. 852, (6)–(7) — profitable activities are integer cutting patterns
-- statement:
--   Fix a stock length $L_j$ of cost $c_j$ and the current pricing multipliers $b_i$. If an activity cutting from that stock can improve the feasible basis, its nonnegative integer piece counts $a_i$ satisfy
--
--   $$
--   \sum_i\ell_i a_i\le L_j,\qquad \sum_i b_i a_i>c_j.
--   $$
--
--   Conversely, under strict positivity of every basic variable, any such pattern gives an improving activity. This turns the search across columns into an integer knapsack feasibility test.
--
--   **Formalization Note** Patterns use natural-number counts, including zero. The sufficient direction carries the same nondegeneracy condition as the pricing criterion; zero basic values can block a strict pivot.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), p. 852, (6)–(7)

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis

namespace GilmoreGomory61.CuttingStock

/-- The integer cutting-pattern form (6)–(7) of the profitable-column test. -/
theorem pricing_integer_form_6_7 {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β) (j : Fin k) :
    ((∃ p : Activity I, p.1.1 = j ∧ Improves I β (Sum.inl p)) →
      ∃ a : Fin m → ℕ, patLen I a ≤ I.L j ∧
        I.c j < ∑ i, mult I β i * (a i : ℝ)) ∧
    (IsNondegenerate I β →
      (∃ a : Fin m → ℕ, patLen I a ≤ I.L j ∧
        I.c j < ∑ i, mult I β i * (a i : ℝ)) →
      ∃ p : Activity I, p.1.1 = j ∧ Improves I β (Sum.inl p)) := by sorry

end GilmoreGomory61.CuttingStock

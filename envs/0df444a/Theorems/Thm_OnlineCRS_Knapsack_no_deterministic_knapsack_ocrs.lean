-- Prove2me | Theorems.Thm_OnlineCRS_Knapsack_no_deterministic_knapsack_ocrs
-- name    : OnlineCRS.Knapsack.no_deterministic_knapsack_ocrs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:45.118363+00:00
-- url     : https://prove2.me/theorems/676b07ec-8012-44a7-9f07-d00ef2f66d9c
-- title:
--   Proposition 2.8 — a knapsack obstruction for deterministic greedy OCRSs
-- statement:
--   For every integer $n\ge1$, there is a unit-capacity knapsack constraint on $n$ elements, with sizes in $[0,1]$, such that no deterministic greedy OCRS for its natural polytope is $(b,c)$-selectable for $b\in[0,1]$ and $c>(1-b)^{n-1}$:
--
--   $$\forall n\ge1\;\exists s\;\forall b\in[0,1]\;\forall c>(1-b)^{n-1},\quad \neg\,\exists\text{ a deterministic $(b,c)$-selectable greedy OCRS for }P_s.$$
--
--   The proposition explains why the randomized construction of Theorem 2.9 is necessary for a constant bound independent of the ground-set size.
--
--   **Formalization Note** At $n=1$, the requested strict inequality is $c>1$, so the assertion is vacuous for possible selectability probabilities, as in the source.
-- source:
--   arXiv:1508.00142v2, Proposition 2.8, p. 14

import Mathlib
import Definitions.Def_OnlineCRS_Knapsack_Model

namespace OnlineCRS.Knapsack

/-- Proposition 2.8, p. 14: for each positive ground-set size there is a knapsack
constraint that defeats every deterministic greedy OCRS above `(1-b)^(n-1)`. -/
theorem no_deterministic_knapsack_ocrs (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Fin n → ℝ, (∀ e, 0 ≤ s e ∧ s e ≤ 1) ∧
      ∀ (fam : (Fin n → ℝ) → Finset (Finset (Fin n))) (b c : ℝ),
        0 ≤ b → b ≤ 1 → (1 - b) ^ (n - 1) < c →
          ¬ OnlineCRS.Matroid.IsSelectableDet (knapsackFeasible s) (knapsackPolytope s) b c fam := by sorry

end OnlineCRS.Knapsack

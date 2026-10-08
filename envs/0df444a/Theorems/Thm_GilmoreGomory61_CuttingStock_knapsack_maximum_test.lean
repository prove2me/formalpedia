-- Prove2me | Theorems.Thm_GilmoreGomory61_CuttingStock_knapsack_maximum_test
-- name    : GilmoreGomory61.CuttingStock.knapsack_maximum_test
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:11:19.52278+00:00
-- url     : https://prove2.me/theorems/76fcea32-2d49-463e-ac03-f51d710ce00f
-- title:
--   pp. 852–853 — a maximizing pattern decides the pricing inequalities
-- statement:
--   Suppose all piece lengths are positive and the available stock length $L$ is nonnegative. For any multipliers $b_i$ there is a feasible nonnegative integer pattern $a^*$ attaining the maximum price
--
--   $$
--   F_m(L)=\max_{\sum_i\ell_i a_i\le L}\sum_i b_i a_i.
--   $$
--
--   For any stock cost $c$, a pattern satisfying both the length constraint and $\sum_i b_i a_i>c$ exists exactly when this maximizing pattern has price greater than $c$. Thus one maximum calculation decides whether the paper's inequalities (6)–(7) are compatible.
--
--   **Formalization Note** Positive lengths make the feasible pattern set finite, and $L\ge0$ makes it nonempty. The page first says “positive integers” but immediately selects “nonnegative integers”; zero counts are allowed here. The maximum is compared through the extended-real value $F_m$.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), pp. 852–853, after (7)

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Knapsack

namespace GilmoreGomory61.CuttingStock

/-- A maximum pattern tests the compatibility of (6) and (7), pp. 852–853. -/
theorem knapsack_maximum_test {m k : ℕ} (I : Instance m k)
    (hℓ : ∀ i, 0 < I.ℓ i) (b : Fin m → ℝ) (L c : ℝ) (hL : 0 ≤ L) :
    ∃ aStar : Fin m → ℕ,
      patLen I aStar ≤ L ∧
      (∀ a : Fin m → ℕ, patLen I a ≤ L →
        (∑ i, b i * (a i : ℝ)) ≤ ∑ i, b i * (aStar i : ℝ)) ∧
      knapF I b m L = ((∑ i, b i * (aStar i : ℝ) : ℝ) : EReal) ∧
      ((∃ a : Fin m → ℕ, patLen I a ≤ L ∧
        c < ∑ i, b i * (a i : ℝ)) ↔ c < ∑ i, b i * (aStar i : ℝ)) := by sorry

end GilmoreGomory61.CuttingStock

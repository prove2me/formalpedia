-- Prove2me | Theorems.Thm_GenericBudgets_MaximinShare_total_price_le
-- name    : GenericBudgets.MaximinShare.total_price_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:12.504694+00:00
-- url     : https://prove2.me/theorems/3f2716a4-ce20-420a-b240-4677b9bf839f
-- title:
--   Proof of Proposition 3.2 — total item price is within total budget
-- statement:
--   Suppose $(S,p)$ is a competitive equilibrium for a finite allocation of all items, with agent budgets $b_i$. The sum of all item prices does not exceed the sum of the budgets:
--
--   $$
--   P:=\sum_{j\in M}p_j\le\sum_{i\in N}b_i.
--   $$
--
--   This accounts for every item exactly once and bounds the price available to any partition of the items.
--
--   **Formalization Note** The paper normalizes $\sum_i b_i=1$ after this inequality. The theorem states the underlying sum form, which needs no normalization assumption; complete allocation is built into the allocation function.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 9, proof of Proposition 3.2, sentence 2

import Mathlib
import Definitions.Def_GenericBudgets_MaximinShare_Setting

namespace GenericBudgets.MaximinShare

/-- Proof of Proposition 3.2, p. 9: all items are purchased within agents' budgets. -/
theorem total_price_le {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (b : Fin n → ℝ) (σ : Fin m → Fin n) (p : Fin m → ℝ)
    (hCE : IsCE v b σ p) : GenericBudgets.AlmostEqual.price p Finset.univ ≤ ∑ i, b i := by sorry

end GenericBudgets.MaximinShare

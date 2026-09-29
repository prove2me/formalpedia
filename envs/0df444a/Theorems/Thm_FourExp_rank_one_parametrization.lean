-- Prove2me | Theorems.Thm_FourExp_rank_one_parametrization
-- name    : FourExp.rank_one_parametrization
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T06:23:12.315816+00:00
-- url     : https://prove2.me/theorems/30f831f0-d392-4e30-aa69-dee7d4b3ba65
-- title:
--   A rank-one matrix of logarithms factors as an outer product of independent pairs
-- statement:
--   **A rank-one $2\times 2$ matrix of logarithms, written as $x_iy_j$.**
--
--   Let $l_{11}, l_{12}, l_{21}, l_{22}$ be non-zero complex numbers with $e^{l_{ij}}$ algebraic, $l_{11}l_{22} = l_{12}l_{21}$, and $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}[l_{ij}] \le 1$. Suppose neither the rows nor the columns are linearly dependent over $\mathbb{Q}$. Then there are $x_1, x_2, y_1, y_2 \in \mathbb{C}$ such that:
--   - $x_1, x_2$ are $\mathbb{Q}$-linearly independent, and so are $y_1, y_2$;
--   - every $e^{x_iy_j}$ is algebraic;
--   - $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}[x_1, x_2, y_1, y_2] \le 1$.
--
--   **Proof idea.** Take $x = (l_{11}, l_{21})$ and $y = (1, r)$ with $r = l_{12}/l_{11}$. Rank one gives $l_{22} = r\,l_{21}$, so $x_iy_j = l_{ij}$.
--   - A relation $a l_{11} + b l_{21} = 0$ would give $a l_{12} + b l_{22} = r(a l_{11} + b l_{21}) = 0$, a row dependence.
--   - $r \in \mathbb{Q}$ would give the column dependence $r l_{11} - l_{12} = r l_{21} - l_{22} = 0$.
--   - The new generators lie in the fraction field of $\mathbb{Q}[l_{ij}]$, which has the same transcendence degree.
--
--   **What it is for.** It is the first child of `FourExp.auxiliary_construction`, turning the matrix hypotheses into the $x_i, y_j$ that Waldschmidt's construction uses.
-- source:
--   Elementary; the reduction of the four exponentials problem to products xᵢyⱼ, as in M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, §I.

import Mathlib

namespace FourExp

theorem rank_one_parametrization :
    ∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ,
      IsAlgebraic ℚ (Complex.exp l₁₁) → IsAlgebraic ℚ (Complex.exp l₁₂) →
      IsAlgebraic ℚ (Complex.exp l₂₁) → IsAlgebraic ℚ (Complex.exp l₂₂) →
      l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 →
      l₁₁ * l₂₂ = l₁₂ * l₂₁ →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
      ¬ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0) →
      ¬ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) →
      ∃ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] ∧ LinearIndependent ℚ ![y₁, y₂] ∧
        (∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j))) ∧
        Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ)) ≤ 1 := by
  sorry

end FourExp

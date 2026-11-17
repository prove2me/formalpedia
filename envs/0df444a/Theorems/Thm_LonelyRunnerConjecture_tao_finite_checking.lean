-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_tao_finite_checking
-- name    : LonelyRunnerConjecture.tao_finite_checking
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-17T01:13:54.310208+00:00
-- url     : https://prove2.me/theorems/3e7950d0-0fee-412e-96ac-d2f84d9bbcd5
-- title:
--   Tao's finite-checking theorem (speeds $\le n^{Cn^2}$)
-- statement:
--   There is a constant $C>0$ such that for every $n_0\ge1$ the following are equivalent: (i) the conjecture holds for all $n\le n_0$; (ii) it holds for all $n\le n_0$ and every $n$-tuple of positive distinct integer speeds with $v_i\le n^{C n^2}$. Thus each fixed case is decidable by a finite check.
--
--   **Formalization Note** Tao's "explicitly computable" constant is a meta-property, stated here as `∃ C > 0`; nonzero integer speeds reduce to positive by $\|tv\|=\|t(-v)\|$. The bound uses real exponentiation `Real.rpow`.
-- source:
--   T. Tao, Some remarks on the lonely runner conjecture, https://arxiv.org/abs/1701.02048 (v4), Theorem 1.3.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem tao_finite_checking :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, 1 ≤ n₀ →
      ((∀ n : ℕ, n ≤ n₀ → LRC n) ↔
       (∀ n : ℕ, n ≤ n₀ → ∀ v : Fin n → ℕ, (∀ i, 0 < v i) →
         Function.Injective v →
         (∀ i, (v i : ℝ) ≤ (n : ℝ) ^ (C * (n : ℝ) ^ 2)) →
         ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤ distToNearestInt (t * (v i : ℝ)))) := by sorry

end LonelyRunnerConjecture

-- Prove2me | Theorems.Thm_LambdaCoalescent_Rates_lemma_18_bijection
-- name    : LambdaCoalescent.Rates.lemma_18_bijection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:38:02.709012+00:00
-- url     : https://prove2.me/theorems/924d5403-2dbb-4f2a-8bb0-761b8026b993
-- title:
--   Lemma 18 — finite measures correspond bijectively to consistent arrays
-- statement:
--   Every finite nonnegative Borel measure $\Lambda$ on $[0,1]$ gives a consistent nonnegative merger-rate array by formula (1). Conversely, every consistent nonnegative array has exactly one such representing measure:
--
--   $$
--   \lambda_{b,k}=\int_{[0,1]}x^{k-2}(1-x)^{b-k}\,\Lambda(dx)\qquad(2\le k\le b).
--   $$
--
--   Both directions and uniqueness express the bijection stated after equation (22) in Lemma 18. The zero measure and zero array are included.
--
--   **Formalization Note** Measures are represented on $\mathbb R$ with zero mass outside $[0,1]$. Finiteness is explicit to ensure the integral denotes the ordinary finite-measure integral.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1882, Lemma 18, second sentence; eq. (1)

import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.Rates

open MeasureTheory

/-- Lemma 18, p. 1882: formula (1) is a bijection. -/
theorem lemma_18_bijection :
    (∀ Λ : Measure ℝ, IsFiniteMeasure Λ → Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      Consistent (lamOf Λ)) ∧
    (∀ lam : ℕ → ℕ → ℝ,
      (∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k) →
      Consistent lam →
      ∃! Λ : Measure ℝ,
        IsFiniteMeasure Λ ∧ Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
          ∀ b k, 2 ≤ k → k ≤ b → lam b k = lamOf Λ b k) := by sorry

end LambdaCoalescent.Rates

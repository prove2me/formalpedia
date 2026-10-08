-- Prove2me | Theorems.Thm_LambdaCoalescent_Rates_eq_24_iff_eq_25
-- name    : LambdaCoalescent.Rates.eq_24_iff_eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:55.738973+00:00
-- url     : https://prove2.me/theorems/ca7c1076-bde2-4149-b26b-76dadb6ce7d7
-- title:
--   Proof of Lemma 18, (24)–(25) — nonnegative array representation
-- statement:
--   Let $(\mu_{i,j})_{i,j\ge0}$ be a nonnegative real array with $\mu_{0,0}=1$. The additive relation
--
--   $$
--   \mu_{i,j}=\mu_{i+1,j}+\mu_{i,j+1}\qquad(i,j\ge0)
--   $$
--
--   holds exactly when there is a probability law $F$ supported on $[0,1]$ such that
--
--   $$
--   \mu_{i,j}=\int_{[0,1]}x^i(1-x)^j\,F(dx)\qquad(i,j\ge0).
--   $$
--
--   This is the array form of the representation used in Lemma 18, after the paper’s reindexing $\mu_{i,j}=\lambda_{i+j+2,i+2}$.
--
--   **Formalization Note** The law $F$ represents the paper’s random variable $X\in[0,1]$; its expectation is written as an integral over $\mathbb R$.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1882, proof of Lemma 18, eqs. (23)–(25)

import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.Rates

open MeasureTheory

/-- Equations (24) and (25), in the proof of Lemma 18, p. 1882. -/
theorem eq_24_iff_eq_25 (μ : ℕ → ℕ → ℝ)
    (hμ : ∀ i j, 0 ≤ μ i j) (h00 : μ 0 0 = 1) :
    (∀ i j, μ i j = μ (i + 1) j + μ i (j + 1)) ↔
      ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ i j, μ i j = ∫ x, x ^ i * (1 - x) ^ j ∂F := by sorry

end LambdaCoalescent.Rates

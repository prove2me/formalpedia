-- Prove2me | Theorems.Thm_KingmanSubadditive_Continuous_skeleton_limit
-- name    : KingmanSubadditive.Continuous.skeleton_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:44:10.732957+00:00
-- url     : https://prove2.me/theorems/0b562115-273d-4c4c-8b66-b3f5d57211ce
-- title:
--   (1.4.8) — the integer-time skeleton converges almost surely and in mean
-- statement:
--   Let $x$ satisfy the hypotheses of Theorem 4, and let $\gamma$ be its continuous-time mean rate. There is an integrable real random variable $\xi$ such that
--
--   $$
--   \frac{x_{0n}}{n}\longrightarrow\xi\quad\text{almost surely and in }L^1(P),
--   \qquad E(\xi)=\gamma,
--   $$
--
--   as the positive integers $n$ tend to infinity. This is the result for the integer-time skeleton that Theorem 4 extends to all real times.
--
--   **Formalization Note** The value of the sequence at $n=0$ is irrelevant to the limit; the statement is about the real-time process sampled at integer times, not a general discrete subadditive theorem.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 889, §1.4, proof of Theorem 4, (1.4.8)

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process

namespace KingmanSubadditive.Continuous

open MeasureTheory Filter Topology

/-- Kingman, §1.4, proof of Theorem 4, (1.4.8), p. 889. This is the
integer-time skeleton of the continuous process, using the continuous
γ from (1.4.1), not a general restatement of Theorem 1. -/
theorem skeleton_limit {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (hsep : IsSeparable P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    ∃ ξ : S → ℝ, Integrable ξ P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => x 0 n ω / (n : ℝ)) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun n : ℕ => ∫ ω, |x 0 n ω / (n : ℝ) - ξ ω| ∂P)
        atTop (𝓝 0) ∧
      (∫ ω, ξ ω ∂P) = gamma P x := by sorry

end KingmanSubadditive.Continuous

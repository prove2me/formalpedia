-- Prove2me | Theorems.Thm_LambdaCoalescent_Rates_theorem_1
-- name    : LambdaCoalescent.Rates.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:57.559237+00:00
-- url     : https://prove2.me/theorems/2d8842b2-9cf2-44dd-855a-1880e94ff620
-- title:
--   Theorem 1 (characterization) — coalescents with merger rates λ_{b,k}
-- statement:
--   Let $\lambda_{b,k}\ge0$ be an array indexed by $2\le k\le b$. For **every** initial partition $\pi$ of the positive integers, a partition-valued coalescent exists, starts at $\pi$, and has finite restrictions that are Markov chains in which each unordered $k$-tuple of the current $b$ blocks merges at rate $\lambda_{b,k}$, if and only if a finite nonnegative Borel measure $\Lambda$ on $[0,1]$ represents all these rates:
--
--   $$
--   \lambda_{b,k}=\int_{[0,1]}x^{k-2}(1-x)^{b-k}\,\Lambda(dx)\qquad(2\le k\le b).
--   $$
--
--   This is the existence-and-rates characterization in the first sentence of Pitman’s Theorem 1. It identifies exactly which arrays can govern a coalescent across all finite restrictions.
--
--   **Formalization Note** Labels are shifted from the paper’s positive integers to zero-based Lean naturals. The process has refining paths with right-continuous finite restrictions, the paper’s stated characterization of cadlag partition paths. The finite Markov laws are pinned down at every finite collection of times by the generator matrix. The sample space is a small Lean type. The later sentences of Theorem 1 about the strong Markov property, Feller semigroup, and weak continuity of the law map are outside this statement.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), pp. 1871–1872, Theorem 1, characterization and eq. (1)

import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.Rates

open MeasureTheory
open scoped NNReal

/-- Theorem 1, pp. 1871–1872: the existence-and-rates characterization. -/
theorem theorem_1 (lam : ℕ → ℕ → ℝ)
    (hlam : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k) :
    (∀ π : PInf,
      ∃ (Ω : Type) (M : MeasurableSpace Ω),
        letI : MeasurableSpace Ω := M
        ∃ (P : Measure Ω) (X : ℝ≥0 → Ω → PInf),
          IsProbabilityMeasure P ∧
          (∀ t, Measurable (X t)) ∧
          (∀ ω, IsCoalescentPath (fun t => X t ω)) ∧
          (∀ ω, X 0 ω = π) ∧
          ∀ n, IsRateChain P (rateMatrix lam n) (restrict n π)
            (fun t ω => restrict n (X t ω))) ↔
      ∃ Λ : Measure ℝ, IsFiniteMeasure Λ ∧ Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ b k, 2 ≤ k → k ≤ b → lam b k = lamOf Λ b k := by sorry

end LambdaCoalescent.Rates

-- Prove2me | Theorems.Thm_NoisyMC_Convex_lemma_19
-- name    : NoisyMC.Convex.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:03.673676+00:00
-- url     : https://prove2.me/theorems/95f2da5c-cfcc-485f-b734-b7307bffd9d5
-- title:
--   Lemma 19 — uniformly over A, B: |p⁻¹‖P_Ω(ABᵀ)‖²_F − ‖ABᵀ‖²_F| ≤ 3n·min{‖A‖²_{2,∞}‖B‖²_F, ‖B‖²_{2,∞}‖A‖²_F}
-- statement:
--   Let $\Omega\subseteq\{1,\dots,n\}^2$ contain each index independently with probability $p$ (Assumption 1(a)), and suppose $n^2p\ge Cn\log n$ for a sufficiently large constant $C>0$. Then with probability exceeding $1-O(n^{-10})$,
--
--   $$\Big|p^{-1}\|\mathcal P_\Omega(AB^\top)\|_F^2-\|AB^\top\|_F^2\Big|\le3n\min\big\{\|A\|_{2,\infty}^2\|B\|_F^2,\ \|B\|_{2,\infty}^2\|A\|_F^2\big\}$$
--
--   holds simultaneously for all $A,B\in\mathbb R^{n\times r}$.
--
--   The estimate controls the sampled energy of a low-rank product whose factors have small rows. It is one ingredient of the uniform injectivity bound (Lemma 7).
--
--   **Formalization Note.** There are $C,C_{\rm fail}>0$ and $n_0$ such that for every $n\ge n_0$, every $r\ge1$, $0<p\le1$ and every sampling model with $n^2p\ge Cn\log n$, the event "for all $A,B$, the inequality holds" fails with (outer) probability at most $C_{\rm fail}n^{-10}$. The quantifier over $A,B$ is inside the event. The constant $3n$ is the paper's.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 62, Lemma 19

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Lemma 19 (p. 62). There are constants `C, C_fail > 0` and `n₀` such that for every `n ≥ n₀`,
`r ≥ 1`, `0 < p ≤ 1` and every Bernoulli(`p`) sampling pattern (Assumption 1(a)) with
`n² p ≥ C n log n`: with probability at least `1 − C_fail n^{-10}`, simultaneously for all
`A, B ∈ ℝ^{n×r}`,
`|p⁻¹ ‖P_Ω(A Bᵀ)‖_F² − ‖A Bᵀ‖_F²| ≤ 3n min{‖A‖_{2,∞}² ‖B‖_F², ‖B‖_{2,∞}² ‖A‖_F²}`. -/
theorem lemma_19 :
    ∃ C : ℝ, 0 < C ∧ ∃ Cfail : ℝ, 0 < Cfail ∧
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ r : ℕ, 1 ≤ r →
    ∀ p : ℝ, 0 < p → p ≤ 1 →
    ∀ {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp) [IsProbabilityMeasure P]
      (δ : Fin n × Fin n → Ωp → Bool),
      SamplingModel P p δ →
      C * n * Real.log n ≤ (n : ℝ) ^ 2 * p →
      P {ω | ¬ ∀ A B : RealMatrix n r,
          |p⁻¹ * frobeniusNorm (samplingProjection (obsSet δ ω) (A * B.transpose)) ^ 2 -
              frobeniusNorm (A * B.transpose) ^ 2| ≤
            3 * n * min (twoInfNorm A ^ 2 * frobeniusNorm B ^ 2)
              (twoInfNorm B ^ 2 * frobeniusNorm A ^ 2)} ≤
        ENNReal.ofReal (Cfail / (n : ℝ) ^ 10) := by sorry

end NoisyMC.Convex

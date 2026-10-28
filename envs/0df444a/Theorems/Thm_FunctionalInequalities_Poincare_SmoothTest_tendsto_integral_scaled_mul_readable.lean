-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_tendsto_integral_scaled_mul_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.tendsto_integral_scaled_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:37.039424+00:00
-- url     : https://prove2.me/theorems/068f0f8e-b98a-4f43-90a9-f224447633d6
-- title:
--   First and Second Integral Convergence Under Scaled Cutoffs
-- statement:
--   This statement gives convergence of the first and second integrals of cutoff products.
--
--   Let $E$ be a real inner product space with its Borel measurable structure, let $\mu$ be a finite measure on $E$, and let $f:E\to\mathbb R$ satisfy `MemLp f 2 μ`, including almost-everywhere strong measurability and finite $L^2$ seminorm. Write $\chi_R$ for `Energy.Euclidean.LipschitzApproximation.scaled R`.
--
--   Both limits hold as $n\in\mathbb N$ tends to infinity:
--   $$
--   \int\chi_{n+1}f\,d\mu\longrightarrow\int f\,d\mu,
--   \qquad
--   \int(\chi_{n+1}f)^2\,d\mu\longrightarrow\int f^2\,d\mu.
--   $$
--   These two scalar convergence statements support variance approximation by cutoff functions.
--
--   **Formalization Note** Neither completeness nor finite dimensionality of $E$ is assumed here. The conclusion is a conjunction of integral limits, not a statement of $L^2$-norm convergence.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_integral_scaled_mul {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
--       (hf : MemLp f 2 μ) :
--       Tendsto (fun n : ℕ => ∫ x, Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x ∂μ)
--           atTop (𝓝 (∫ x, f x ∂μ)) ∧
--         Tendsto (fun n : ℕ =>
--             ∫ x, (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2 ∂μ)
--           atTop (𝓝 (∫ x, f x ^ 2 ∂μ))
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/SmoothTest/WeakLimit`](https://prove2.me/theorems/e4730d77-c352-491a-b178-72fb5045a2b9).
--
--   Definition modules: [`Analysis/Cutoff/SmoothBall`](https://prove2.me/theorems/e579c572-cae8-4aab-bbfa-980860e9fc63).
--
--   Previous: [`Admissible.of_contDiff_hasCompactSupport`](https://prove2.me/theorems/7f79ab39-6c03-4d68-870d-2dd02d1e1b0b) · Next: [`norm_gradient_scaled_mul_sq_le`](https://prove2.me/theorems/1194b2a8-bd6e-4efd-bc86-f6b48715f7e0).
--
--   [Source excerpt, lines 201–207](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L201-L207) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L198-L324 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.tendsto_integral_scaled_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

open MeasureTheory ProbabilityTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
variable [FiniteDimensional ℝ E]
omit [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Poincare.SmoothTest.tendsto_integral_scaled_mul_readable {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Tendsto (fun n : ℕ => ∫ x, Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x ∂μ)
        atTop (𝓝 (∫ x, f x ∂μ)) ∧
      Tendsto (fun n : ℕ =>
          ∫ x, (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2 ∂μ)
        atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by sorry

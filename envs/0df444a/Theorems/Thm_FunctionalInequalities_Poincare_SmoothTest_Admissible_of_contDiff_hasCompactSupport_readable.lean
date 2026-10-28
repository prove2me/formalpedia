-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_Admissible_of_contDiff_hasCompactSupport_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:38.832323+00:00
-- url     : https://prove2.me/theorems/7f79ab39-6c03-4d68-870d-2dd02d1e1b0b
-- title:
--   Compactly Supported Smooth Functions Are Admissible
-- statement:
--   This auxiliary statement supplies admissible smooth Poincaré tests for every finite measure.
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure, let $\mu$ be a finite measure on $E$, and let $f:E\to\mathbb R$ be $C^\infty$ with compact support.
--
--   Then $f$ is admissible (`Poincare.SmoothTest.Admissible`):
--   $$
--   f\in C^\infty(E),\qquad f\in L^2(\mu),\qquad
--   \bigl(x\mapsto\|\nabla f(x)\|^2\bigr)\in L^1(\mu).
--   $$
--   This provides tests usable in the smooth-test Poincaré inequality without a probability or density assumption on the measure.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Admissible.of_contDiff_hasCompactSupport {μ : Measure E} [IsFiniteMeasure μ]
--       {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Admissible μ f
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/SmoothTest/WeakLimit`](https://prove2.me/theorems/e4730d77-c352-491a-b178-72fb5045a2b9).
--
--   Definition modules: [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f).
--
--   Previous: [`variance_le_mul_energy_of_tendsto`](https://prove2.me/theorems/0405b112-362b-4b97-b8df-8b73697c57e3) · Next: [`tendsto_integral_scaled_mul`](https://prove2.me/theorems/068f0f8e-b98a-4f43-90a9-f224447633d6).
--
--   [Source excerpt, lines 159–160](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L159-L160) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L158-L186 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport_readable {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Admissible μ f := by sorry

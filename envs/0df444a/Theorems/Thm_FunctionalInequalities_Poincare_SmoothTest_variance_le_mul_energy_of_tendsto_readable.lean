-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_variance_le_mul_energy_of_tendsto_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.variance_le_mul_energy_of_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:50.680048+00:00
-- url     : https://prove2.me/theorems/0405b112-362b-4b97-b8df-8b73697c57e3
-- title:
--   Weak-Limit Passage for a Fixed Compactly Supported Smooth Test
-- statement:
--   This is a fixed-test weak-limit transfer statement associated with Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered), and its regular-approximation reduction.
--
--   Let $E$ be a complete real inner product space with its Borel measurable structure. Assume:
--
--   1. Probability measures $\mu_j$ converge weakly to a probability measure $\mu$ as $j\in\mathbb N$ tends to infinity.
--   2. Real numbers $C_j$ converge to $C\in\mathbb R$.
--   3. $f:E\to\mathbb R$ is $C^\infty$ with compact support.
--   4. For every $j$, $\operatorname{Var}_{\mu_j}(f)\le C_j\int\|\nabla f\|^2\,d\mu_j$.
--
--   Then
--   $$
--   \operatorname{Var}_\mu(f)\le C\int\|\nabla f\|^2\,d\mu.
--   $$
--   This transfers the inequality for the specified test, rather than asserting a bound for all tests at once.
--
--   **Formalization Note** The energy is `Poincare.SmoothTest.energy`, and variance is `ProbabilityTheory.variance`. No finite-dimensionality, log-concavity, or nonnegativity assumption on $C_j$ or $C$ is present.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem variance_le_mul_energy_of_tendsto {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
--       (hlim : Tendsto μs atTop (𝓝 μ)) {Cseq : ℕ → ℝ} {C : ℝ} (hC : Tendsto Cseq atTop (𝓝 C))
--       {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
--       (h : ∀ j, variance f (μs j : Measure E) ≤ Cseq j * energy (μs j : Measure E) f) :
--       variance f (μ : Measure E) ≤ C * energy (μ : Measure E) f
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/SmoothTest/WeakLimit`](https://prove2.me/theorems/e4730d77-c352-491a-b178-72fb5045a2b9).
--
--   Definition modules: [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f).
--
--   Next: [`Admissible.of_contDiff_hasCompactSupport`](https://prove2.me/theorems/7f79ab39-6c03-4d68-870d-2dd02d1e1b0b).
--
--   [Source excerpt, lines 31–35](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L31-L35) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L29-L152 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.variance_le_mul_energy_of_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Poincare.SmoothTest.variance_le_mul_energy_of_tendsto_readable {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hlim : Tendsto μs atTop (𝓝 μ)) {Cseq : ℕ → ℝ} {C : ℝ} (hC : Tendsto Cseq atTop (𝓝 C))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (h : ∀ j, variance f (μs j : Measure E) ≤ Cseq j * energy (μs j : Measure E) f) :
    variance f (μ : Measure E) ≤ C * energy (μ : Measure E) f := by sorry

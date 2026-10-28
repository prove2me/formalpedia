-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_preEnergy_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:54.353965+00:00
-- url     : https://prove2.me/theorems/694b924d-e8c7-4e05-a535-534efe21d525
-- title:
--   Smooth-Test Bounds Equivalent to Smooth Pre-Energy Test-Family Bounds
-- statement:
--   This statement identifies two fixed-constant formulations of the smooth-gradient Poincaré inequality.
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure and a second-countable topology. Let $\mu$ be any probability measure on $E$ and $C\in[0,\infty)$. Let $\mathcal T_\mu$ be the test family `Poincare.TestFamily.ofPreEnergy μ (Energy.SmoothGradient.preEnergy μ)`.
--
--   Then
--   $$
--   \operatorname{SmoothTest.Holds}(\mu,C)
--   \quad\Longleftrightarrow\quad
--   \operatorname{TestFamily.Holds}(\mathcal T_\mu,C).
--   $$
--   The left side is `Poincare.SmoothTest.Holds`: variance is at most $C\int\|\nabla f\|^2\,d\mu$ for every $C^\infty$ function $f\in L^2(\mu)$ with integrable squared gradient. The right side is the corresponding inequality on the concrete pre-energy test family.
--
--   This equivalence connects the concrete smooth-test formulation to the test-family interface, without asserting an identification with a relaxed or literature constant.
--
--   **Formalization Note** $C$ is `NNReal` and is coerced to $\mathbb R$ on the left. No moment, log-concavity, density, or positive-dimension assumption is imposed on $\mu$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem holds_iff_preEnergy (C : NNReal) :
--       Holds (μ : Measure E) (C : ℝ) ↔
--         (TestFamily.ofPreEnergy μ (Energy.SmoothGradient.preEnergy μ)).Holds C
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/SmoothTest/Comparison`](https://prove2.me/theorems/2cc5136c-e250-45ef-8770-d1af91bb9c3f).
--
--   Definition modules: [`Poincare/SmoothTest/Optimal`](https://prove2.me/theorems/1bd7b12a-ba10-47ca-83e9-4d99a34876b9), [`Poincare/Relaxation`](https://prove2.me/theorems/33b81a93-0d3f-4459-b2f9-a34a6959e52b), [`Energy/SmoothGradient/Basic`](https://prove2.me/theorems/230d76a3-8a28-41f5-a6c8-38e17a1abcdd), [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f).
--
--   [Source excerpt, lines 38–40](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/Comparison.lean#L38-L40) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Comparison.lean#L36-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Comparison`, declaration `FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Comparison

open MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : MeasureTheory.ProbabilityMeasure E)

theorem FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy_readable (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔
      (TestFamily.ofPreEnergy μ (Energy.SmoothGradient.preEnergy μ)).Holds C := by sorry

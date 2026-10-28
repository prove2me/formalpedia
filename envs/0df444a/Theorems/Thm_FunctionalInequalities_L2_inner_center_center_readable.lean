-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_inner_center_center_readable
-- name    : FunctionalInequalities.L2.inner_center_center_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:08.871709+00:00
-- url     : https://prove2.me/theorems/abb6082d-7b62-4620-a9a1-7ab8a33a4366
-- title:
--   Inner Product of Centered $L^2$ Functions
-- statement:
--   This statement gives the inner-product identity for centered functions on a probability space.
--
--   Let $\mu$ be a probability measure on a measurable space and let $f,g\in L^2(\mu)$. With `center` defined by subtracting the respective means,
--
--   $$\left\langle f-\int f\,d\mu,\,g-\int g\,d\mu\right\rangle_{L^2(\mu)}
--   =\langle f,g\rangle_{L^2(\mu)}-\left(\int f\,d\mu\right)\left(\int g\,d\mu\right).$$
--
--   This elementary identity is reusable for variance, orthogonality, and centered-gradient calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_center_center (μ : ProbabilityMeasure α)
--       (f g : Lp ℝ 2 (μ : Measure α)) :
--       inner ℝ (center μ f) (center μ g) =
--         inner ℝ f g - mean μ f * mean μ g
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Next: [`tendsto_variance_finite_linear_combination`](https://prove2.me/theorems/dd0e74f6-3d24-47af-bea4-9a629c78de4f).
--
--   [Source excerpt, lines 188–191](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/MeanVariance.lean#L188-L191) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/MeanVariance.lean#L187-L203 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.MeanVariance`, declaration `FunctionalInequalities.L2.inner_center_center`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance

open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

theorem FunctionalInequalities.L2.inner_center_center_readable (μ : ProbabilityMeasure α)
    (f g : Lp ℝ 2 (μ : Measure α)) :
    inner ℝ (center μ f) (center μ g) =
      inner ℝ f g - mean μ f * mean μ g := by sorry

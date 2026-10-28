-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_norm_posteriorMean_le_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.norm_posteriorMean_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:58.093872+00:00
-- url     : https://prove2.me/theorems/1ba79c02-44ff-4be0-ac9c-b3cb262c225b
-- title:
--   Posterior Mean Radius Bound
-- statement:
--   This statement bounds the norm of the posterior mean by the radius of a ball containing the prior support.
--
--   Let $\mu$ be a probability law on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$. Let $r\ge0$ and assume
--
--   $$
--   \operatorname{supp}(\mu)\subseteq\overline{B}(0,r).
--   $$
--
--   For every posterior parameter $p=(c,Q)$, the posterior mean satisfies
--
--   $$
--   \left\|a(\mu;c,Q)\right\|\le r,
--   $$
--
--   where $a(\mu;c,Q)$ is `posteriorMean`. The estimate is an a-priori geometric bound used in posterior energy arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_posteriorMean_le {r : ℝ} (hr : 0 ≤ r)
--       (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) (p : Param n) :
--       ‖posteriorMean μ p.1 p.2‖ ≤ r
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Energy/Bound`](https://prove2.me/theorems/4ab05ed1-3d8d-48ff-a6a8-e41faa7f3068).
--
--   Definition modules: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74).
--
--   Previous: [`posterior_energy_transfer`](https://prove2.me/theorems/d67b027d-a7b5-4e5f-9323-596964225290) · Next: [`exists_cumulantEnergy_le`](https://prove2.me/theorems/5481f760-ae1c-4c90-be25-67d353f6a39c).
--
--   [Source excerpt, lines 173–175](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Bound.lean#L173-L175) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Bound.lean#L172-L190 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Bound`, declaration `FunctionalInequalities.KLS.BKL.Localization.norm_posteriorMean_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Bound

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
variable {n : ℕ}
variable (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.norm_posteriorMean_le_readable {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) (p : Param n) :
    ‖posteriorMean μ p.1 p.2‖ ≤ r := by sorry

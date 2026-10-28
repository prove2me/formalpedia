-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_biconjugate_lowerTruncate_potentialIntegrable_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:59.906877+00:00
-- url     : https://prove2.me/theorems/df218836-ab33-4397-add0-3cff5ff33b47
-- title:
--   Integrability of the Truncated Biconjugate
-- statement:
--   This proves admissibility of the actual biconjugate of a lower truncation.
--
--   Let $\mu$ be a nonzero finite Borel measure on a real inner-product space, let $f:E\to\overline{\mathbb R}$ be potential-integrable, and let $M\in\mathbb R$. Then
--
--   $$
--   \operatorname{Leg}\!\left(\operatorname{Leg}(\max(f,-M))\right)
--   $$
--
--   is potential-integrable with respect to $\mu$. The statement includes the required Borel measurability and finite-measure assumptions and derives integrability from the truncation bounds rather than requiring it separately for the biconjugate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem biconjugate_lowerTruncate_potentialIntegrable [IsFiniteMeasure μ]
--       (f : E → EReal) (M : ℝ) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ) :
--       PotentialIntegrable (legendre (legendre (lowerTruncate f M))) μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Integrability`](https://prove2.me/theorems/0f56c51b-1f88-4bf0-b556-0b95a64eb739).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81), [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c).
--
--   Supporting theorems: [`lowerTruncate_convexification`](https://prove2.me/theorems/1d40fba2-adb7-47d5-9def-9ed116ba3cc6).
--
--   [Source excerpt, lines 71–73](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Integrability.lean#L71-L73) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Integrability.lean#L68-L101 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Integrability`, declaration `FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Integrability

open FunctionalInequalities.Analysis
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E}

theorem FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable_readable [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ) :
    PotentialIntegrable (legendre (legendre (lowerTruncate f M))) μ := by sorry

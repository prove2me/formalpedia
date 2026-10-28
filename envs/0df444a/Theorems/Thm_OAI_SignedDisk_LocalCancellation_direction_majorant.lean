-- Prove2me | Theorems.Thm_OAI_SignedDisk_LocalCancellation_direction_majorant
-- name    : OAI.SignedDisk.LocalCancellation.direction_majorant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:33:15.130994+00:00
-- url     : https://prove2.me/theorems/d3a7ee27-f441-4adf-af1f-0daaf21abdf4
-- title:
--   OAI.SignedDisk.LocalCancellation.direction_majorant: intermediate lemma from OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Endpoint Gradient Bound for the Centered Disk Maximal Operator*, OpenAI Math Release, September 26, 2026, result family 85, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SignedDisk.LocalCancellation.direction_majorant` of [lean/OAI/Analysis/SignedDisk/SignedDisk/DiskScales3.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SignedDisk/SignedDisk/DiskScales3.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SignedDisk.LocalCancellation`, with `open MeasureTheory Set`, `open scoped ENNReal NNReal Topology ContDiff`, `open scoped RealInnerProductSpace`, `open MeasureTheory Set Filter`, `open scoped Topology ENNReal`, `open scoped Real RealInnerProductSpace`, `open scoped Topology RealInnerProductSpace ContDiff`, `open scoped Topology Interval NNReal`, `open scoped Topology NNReal Real`, `open DiskKernels DiskMoments DiskGeometry DiskScales`):
--
--   ```lean
--   theorem direction_majorant {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
--       ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {e : ℂ} (a : ConeDensity e κ)
--         (b : ι → ErrorPiece Cs), ‖e‖ = 1 →
--         ∀ g : ℂ → ℝ, ContDiff ℝ 1 g → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
--         ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
--           (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
--           ∀ x, (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
--             ∀ r, NeighborhoodRadius g x r →
--               ENNReal.ofReal (max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y))) ≤ F x
--   ```
--
--   **Definitions.** The statement is written with `OAI.SignedDisk.DiskMoments.NeighborhoodRadius`, `OAI.SignedDisk.LocalCancellation.ConeDensity`, `OAI.SignedDisk.LocalCancellation.ErrorPiece` and `OAI.SignedDisk.LocalCancellation.errorPrice` (definitions bundle `OAIW2SD000` of this split).
--
--   **Used by.** The proof of `OAI.SignedDisk.CommonPrices.patched_unfavorable` of this split imports it.
-- source:
--   OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 85; paper: https://github.com/openai/math; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SignedDisk/SignedDisk/DiskScales3.lean (declaration OAI.SignedDisk.LocalCancellation.direction_majorant)

import Mathlib
import Definitions.Def_OAIW2SD000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales

theorem direction_majorant {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {e : ℂ} (a : ConeDensity e κ)
      (b : ι → ErrorPiece Cs), ‖e‖ = 1 →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
      ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
        (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
        ∀ x, (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
          ∀ r, NeighborhoodRadius g x r →
            ENNReal.ofReal (max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y))) ≤ F x := by
  sorry

end LocalCancellation

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

open MeasureTheory Set
open scoped ENNReal NNReal

end SignedDisk

end

end OAI
end

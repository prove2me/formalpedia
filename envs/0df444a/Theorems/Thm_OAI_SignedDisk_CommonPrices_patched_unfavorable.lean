-- Prove2me | Theorems.Thm_OAI_SignedDisk_CommonPrices_patched_unfavorable
-- name    : OAI.SignedDisk.CommonPrices.patched_unfavorable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:31:52.235217+00:00
-- url     : https://prove2.me/theorems/088f695f-ce31-4efe-b8da-914c1d8584fb
-- title:
--   OAI.SignedDisk.CommonPrices.patched_unfavorable: intermediate lemma from OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Endpoint Gradient Bound for the Centered Disk Maximal Operator*, OpenAI Math Release, September 26, 2026, result family 85, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SignedDisk.CommonPrices.patched_unfavorable` of [lean/OAI/Analysis/SignedDisk/SignedDisk/CommonPrices4.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SignedDisk/SignedDisk/CommonPrices4.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SignedDisk.CommonPrices`, with `open MeasureTheory Set`, `open scoped ENNReal NNReal Topology ContDiff`, `open scoped RealInnerProductSpace`, `open MeasureTheory Set Filter`, `open scoped Topology ENNReal`, `open scoped Real RealInnerProductSpace`, `open scoped Topology RealInnerProductSpace ContDiff`, `open scoped Topology Interval NNReal`, `open scoped Topology NNReal Real`, `open MeasureTheory Set Metric`, `open scoped ENNReal NNReal Topology`, `open scoped ENNReal NNReal`, `open Finset`, `open scoped ENNReal NNReal RealInnerProductSpace`, `open scoped ContDiff`, `open MeasureTheory Set Metric Filter`, `open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology`, `open MeasureTheory MeasureTheory.Measure Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff`, `open MeasureTheory Set Metric Filter Finset`, `open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels`):
--
--   ```lean
--   theorem patched_unfavorable : ∃ C : ℝ, 0 < C ∧
--       ∀ {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R) (hN : R/base+1 ≤ (N:ℝ))
--       {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
--       (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
--       (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
--       ∃ H : ℕ → Label → ℂ → ℝ,
--         (∀ j n x, 0 ≤ H j n x) ∧ (∀ j n, Integrable (H j n)) ∧
--         (∀ᵐ x, ∀ j n t, PhysicalNeighborhoodRadius g (scale base j) x t →
--           unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H j n x) ∧
--         (∀ m n, (∑ j ∈ range (m+1), ∫ x, marginal (gradient g) (geometricRadii base m) (m-j) x n*H j n x) ≤
--           C*(∫ y, ‖gradient g y‖))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SignedDisk.ActualLabels.Label`, `OAI.SignedDisk.ActualLabels.geometricRadii`, `OAI.SignedDisk.ActualLabels.instFintypeLabel`, `OAI.SignedDisk.ActualLabels.marginal`, `OAI.SignedDisk.DiskMoments.PhysicalNeighborhoodRadius`, `OAI.SignedDisk.DiskMoments.signedAverage`, `OAI.SignedDisk.DyadicHats.scale`, `OAI.SignedDisk.SignedRuns.unfavorable` and `OAI.SignedDisk.FiniteLabels.Law` (definitions bundle `OAIW2SD000` of this split).
--
--   **Used by.** The proof of `OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band` of this split imports it.
-- source:
--   OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 85; paper: https://github.com/openai/math; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SignedDisk/SignedDisk/CommonPrices4.lean (declaration OAI.SignedDisk.CommonPrices.patched_unfavorable)

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
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

theorem patched_unfavorable : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R) (hN : R/base+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    ∃ H : ℕ → Label → ℂ → ℝ,
      (∀ j n x, 0 ≤ H j n x) ∧ (∀ j n, Integrable (H j n)) ∧
      (∀ᵐ x, ∀ j n t, PhysicalNeighborhoodRadius g (scale base j) x t →
        unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H j n x) ∧
      (∀ m n, (∑ j ∈ range (m+1), ∫ x, marginal (gradient g) (geometricRadii base m) (m-j) x n*H j n x) ≤
        C*(∫ y, ‖gradient g y‖)) := by
  sorry

end CommonPrices

end SignedDisk

end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_SignedDisk_CommonPrices_physical_size_price
-- name    : OAI.SignedDisk.CommonPrices.physical_size_price
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:31:49.131521+00:00
-- url     : https://prove2.me/theorems/d4ff5c92-235c-4b23-943b-5f477e1e6997
-- title:
--   OAI.SignedDisk.CommonPrices.physical_size_price: intermediate lemma from OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Endpoint Gradient Bound for the Centered Disk Maximal Operator*, OpenAI Math Release, September 26, 2026, result family 85, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SignedDisk.CommonPrices.physical_size_price` of [lean/OAI/Analysis/SignedDisk/SignedDisk/PhysicalCells1.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SignedDisk/SignedDisk/PhysicalCells1.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SignedDisk.CommonPrices`, with `open MeasureTheory Set`, `open scoped ENNReal NNReal Topology ContDiff`, `open scoped RealInnerProductSpace`, `open MeasureTheory Set Filter`, `open scoped Topology ENNReal`, `open scoped Real RealInnerProductSpace`, `open scoped Topology RealInnerProductSpace ContDiff`, `open scoped Topology Interval NNReal`, `open scoped Topology NNReal Real`, `open MeasureTheory Set Metric`, `open scoped ENNReal NNReal Topology`, `open scoped ENNReal NNReal`, `open Finset`, `open scoped ENNReal NNReal RealInnerProductSpace`, `open scoped ContDiff`, `open MeasureTheory Set Metric Filter`, `open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology`, `open MeasureTheory MeasureTheory.Measure Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff`, `open MeasureTheory Set Metric Filter Finset`, `open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces PhysicalCells`):
--
--   ```lean
--   theorem physical_size_price : ∃ C : ℝ, 0 < C ∧
--       ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
--       {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
--       (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
--       (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
--       {n : ℂ}, n ∈ fixedPalette.labels →
--       ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
--         (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
--           (C*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
--         ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
--           PhysicalEndpointRadius g (scale r k) y t →
--           ENNReal.ofReal ‖gradient (fun z => signedAverage g z t) y‖ ≤ F y
--   ```
--
--   **Definitions.** The statement is written with `OAI.SignedDisk.CommonPrices.cellPrice`, `OAI.SignedDisk.CommonPrices.cellRoots`, `OAI.SignedDisk.CommonPrices.rootMass`, `OAI.SignedDisk.ConeCoordinates.fixedPalette`, `OAI.SignedDisk.DiskMoments.PhysicalEndpointRadius`, `OAI.SignedDisk.DiskMoments.signedAverage`, `OAI.SignedDisk.DyadicHats.point`, `OAI.SignedDisk.DyadicHats.scale`, `OAI.SignedDisk.PhysicalCells.cell` and `OAI.SignedDisk.ConeCoordinates.Palette` (definitions bundle `OAIW2SD000` of this split).
--
--   **Used by.** The proof of `OAI.SignedDisk.CommonPrices.physical_joint_price` of this split imports it.
-- source:
--   OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 85; paper: https://github.com/openai/math; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SignedDisk/SignedDisk/PhysicalCells1.lean (declaration OAI.SignedDisk.CommonPrices.physical_size_price)

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
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces PhysicalCells

theorem physical_size_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalEndpointRadius g (scale r k) y t →
        ENNReal.ofReal ‖gradient (fun z => signedAverage g z t) y‖ ≤ F y := by
  sorry

end CommonPrices

end SignedDisk

end

end OAI
end

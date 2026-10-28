-- Prove2me | Theorems.Thm_OAI_CompactMomentVariational_exists_C11_truncated
-- name    : OAI.CompactMomentVariational.exists_C11_truncated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T05:13:59.530877+00:00
-- url     : https://prove2.me/theorems/f7b6d8e3-1acc-4e51-b133-0817de5d3903
-- title:
--   OAI.CompactMomentVariational.exists_C11_truncated: intermediate lemma from OpenAI, The logarithmic Brunn–Minkowski conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogBrunnMinkowski.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The logarithmic Brunn–Minkowski conjecture*, OpenAI Math Release, September 23, 2026, result family 91, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CompactMomentVariational.exists_C11_truncated` of [lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CompactMomentVariational`, with `open Set MeasureTheory Filter`, `open scoped InnerProductSpace Topology NNReal`, `open Set Filter`, `open scoped Topology NNReal`, `open Set MeasureTheory Filter`, `open scoped Topology NNReal ENNReal`, `open scoped ENNReal`, `open scoped InnerProductSpace ContDiff Topology`, `open scoped ENNReal`, `open Set MeasureTheory Filter`, `open scoped ENNReal Topology`, `open WeakMomentBound`):
--
--   ```lean
--   theorem exists_C11_truncated (b : OrthonormalBasis ι ℝ E)
--       {V : E → ℝ} (hV : Continuous V) (hVe : Function.Even V)
--       {ε : ℝ} (hε : 0 < ε)
--       (hcurv : ∀ x y, ε/8*‖x-y‖^2 ≤ (V x+V y)/2-V ((1/2:ℝ) • (x+y)))
--       {R : ℝ≥0} (hR : 0 < R) :
--       ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ Function.Even φ ∧ LipschitzWith R φ ∧
--         ContDiff ℝ 1 φ ∧ LipschitzWith (Real.toNNReal (16/ε)) (gradient φ) ∧
--         (∀ h z, secondDiff φ h z ≤ 4/ε*‖h‖^2) ∧
--         (∃ c > 0, ∃ d : ℝ, ∀ z, c*‖z‖-d ≤ φ z) ∧
--         IsProbabilityMeasure (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) ∧
--         (∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) ∧
--         Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
--           TruncatedMoment.target μ R V
--   ```
--
--   **Definitions.** The statement is written with `OAI.TruncatedMoment.target` and `OAI.WeakMomentBound.secondDiff` (definitions bundle `OAIW2LB000` of this split).
--
--   **Used by.** The proof of `OAI.LogBrunnMinkowski.softVariance` of this split imports it.
-- source:
--   OpenAI, The logarithmic Brunn–Minkowski conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 91; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean (declaration OAI.CompactMomentVariational.exists_C11_truncated)

import Mathlib
import Definitions.Def_OAIW2LB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology NNReal

open Set Filter
open scoped Topology NNReal

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

open scoped ENNReal

open scoped InnerProductSpace ContDiff Topology
open scoped ENNReal

open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CompactMomentVariational
open WeakMomentBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_C11_truncated (b : OrthonormalBasis ι ℝ E)
    {V : E → ℝ} (hV : Continuous V) (hVe : Function.Even V)
    {ε : ℝ} (hε : 0 < ε)
    (hcurv : ∀ x y, ε/8*‖x-y‖^2 ≤ (V x+V y)/2-V ((1/2:ℝ) • (x+y)))
    {R : ℝ≥0} (hR : 0 < R) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ Function.Even φ ∧ LipschitzWith R φ ∧
      ContDiff ℝ 1 φ ∧ LipschitzWith (Real.toNNReal (16/ε)) (gradient φ) ∧
      (∀ h z, secondDiff φ h z ≤ 4/ε*‖h‖^2) ∧
      (∃ c > 0, ∃ d : ℝ, ∀ z, c*‖z‖-d ≤ φ z) ∧
      IsProbabilityMeasure (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) ∧
      (∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) ∧
      Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
        TruncatedMoment.target μ R V := by
  sorry

end CompactMomentVariational
end

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

end

end OAI
end

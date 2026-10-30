-- Prove2me | Theorems.Thm_OAI_Falconer_bounded_chart_regular_fine_gain
-- name    : OAI.Falconer.bounded_chart_regular_fine_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:48:11.877832+00:00
-- url     : https://prove2.me/theorems/eb61f94a-2152-44d4-a486-36b4fae09a51
-- title:
--   OAI.Falconer.bounded_chart_regular_fine_gain: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.bounded_chart_regular_fine_gain` of [lean/OAI/MeasureTheory/Falconer/Geometry/BoundedChartFineGain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Geometry/BoundedChartFineGain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`):
--
--   ```lean
--   theorem bounded_chart_regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
--       ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
--         let Δ := 1/(2:ℝ)^n
--         let ρ := 1/(2:ℝ)^(n+3)
--         let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
--         ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
--         ∀ P : Finset (Space 2), P.Nonempty →
--           InBoundedLineChart P →
--           FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
--           ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
--         ∀ V : Space 2 → Finset (Space 2),
--           (∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
--             FiniteSeparatedAt (Δ^2) (V p) ∧ NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
--             ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
--           ¬ ((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.FiniteSeparatedAt`, `OAI.Falconer.InBoundedLineChart`, `OAI.Falconer.NormalizedFiniteBallBound`, `OAI.Falconer.Space` and `OAI.Falconer.TubeIncident` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.coarsePlanarRound` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.block_cell_power` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Geometry/BoundedChartFineGain.lean (declaration OAI.Falconer.bounded_chart_regular_fine_gain)

import Mathlib
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
attribute [local instance] Classical.propDecidable

theorem bounded_chart_regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let ρ := 1/(2:ℝ)^(n+3)
      let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      ∀ P : Finset (Space 2), P.Nonempty →
        InBoundedLineChart P →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
        ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
          FiniteSeparatedAt (Δ^2) (V p) ∧ NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ ((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 := by
  sorry

end Falconer

end OAI
end

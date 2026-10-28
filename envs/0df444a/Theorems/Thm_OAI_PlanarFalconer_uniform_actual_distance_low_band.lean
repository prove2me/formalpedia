-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_distance_low_band
-- name    : OAI.PlanarFalconer.uniform_actual_distance_low_band
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:56:39.035278+00:00
-- url     : https://prove2.me/theorems/983453b1-d5b7-43b0-af36-2496699fc020
-- title:
--   OAI.PlanarFalconer.uniform_actual_distance_low_band: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_distance_low_band` of [lean/OAI/MeasureTheory/Falconer/Falconer/Fourier/ActualDistanceLowBand.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Fourier/ActualDistanceLowBand.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem uniform_actual_distance_low_band {sig : ℝ} (hsig : 0 < sig)
--       {J : ℕ} (hJ : 0 < J) :
--       ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ],
--         N₀ ≤ d.N → d.sig = sig → d.J = J → d.Q.side = 1 →
--         d.StronglySeparated → d.ρ d.Q.carrierᶜ = 0 → 0 < d.q → d.t ≤ d.N →
--         ∀ v ≤ d.t, (2:ℝ)^(-(d.a:ℝ)) *
--           (∫ r in Icc (-((2:ℝ)^v)) ((2:ℝ)^v), ‖charFun d.weightedDistance r‖^2) ≤
--             (32*binKernelConstant.toReal) *
--               ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.binKernelConstant`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.StronglySeparated`, `OAI.PlanarFalconer.PositiveDistanceData.coincidence` and `OAI.PlanarFalconer.PositiveDistanceData.weightedDistance` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Fourier/ActualDistanceLowBand.lean (declaration OAI.PlanarFalconer.uniform_actual_distance_low_band)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_actual_distance_low_band {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ],
      N₀ ≤ d.N → d.sig = sig → d.J = J → d.Q.side = 1 →
      d.StronglySeparated → d.ρ d.Q.carrierᶜ = 0 → 0 < d.q → d.t ≤ d.N →
      ∀ v ≤ d.t, (2:ℝ)^(-(d.a:ℝ)) *
        (∫ r in Icc (-((2:ℝ)^v)) ((2:ℝ)^v), ‖charFun d.weightedDistance r‖^2) ≤
          (32*binKernelConstant.toReal) *
            ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal := by
  sorry

end PlanarFalconer

end OAI
end

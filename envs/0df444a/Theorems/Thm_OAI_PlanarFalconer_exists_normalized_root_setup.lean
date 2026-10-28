-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_exists_normalized_root_setup
-- name    : OAI.PlanarFalconer.exists_normalized_root_setup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:59:28.321317+00:00
-- url     : https://prove2.me/theorems/4ab6ae0c-f059-4255-b3be-ae160d92ea59
-- title:
--   OAI.PlanarFalconer.exists_normalized_root_setup: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.exists_normalized_root_setup` of [lean/OAI/MeasureTheory/Falconer/Falconer/Frostman/NormalizedRootSetup.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Frostman/NormalizedRootSetup.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set Metric MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem exists_normalized_root_setup (E : Set Plane) (hE : IsCompact E) (hd : 1 < dimH E) :
--       ∃ δ s : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < s ∧
--         ∃ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) ∧
--           dist (Q 0).center (Q 1).center = 250 ∧
--         ∃ μ ν : ProbabilityMeasure Plane,
--           IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
--           (μ : Measure Plane).support ⊆ (fun x : Plane => s • x) '' E ∧
--           (ν : Measure Plane).support ⊆ (fun x : Plane => s • x) '' E ∧
--           (μ : Measure Plane).support ⊆ (Q 0).carrier ∧
--           (ν : Measure Plane).support ⊆ (Q 1).carrier ∧
--           (μ : Measure Plane) (Q 0).carrierᶜ = 0 ∧ (ν : Measure Plane) (Q 1).carrierᶜ = 0 ∧
--         ∃ C : ℝ, 0 < C ∧ BallBound μ (1+δ) C ∧ BallBound ν (1+δ) C ∧
--         ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
--           (∀ x ∈ (μ : Measure Plane).support,
--             sourceDensityNorm (1+δ/8) ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
--           (∀ y ∈ (ν : Measure Plane).support,
--             sourceDensityNorm (1+δ/8) ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.BallBound`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.sourceRadialUnit`, `OAI.PlanarFalconer.DyadicSquare.carrier` and `OAI.PlanarFalconer.DyadicSquare.center` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.sourceDensityNorm` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.mainTarget_proved` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Frostman/NormalizedRootSetup.lean (declaration OAI.PlanarFalconer.exists_normalized_root_setup)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem exists_normalized_root_setup (E : Set Plane) (hE : IsCompact E) (hd : 1 < dimH E) :
    ∃ δ s : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < s ∧
      ∃ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) ∧
        dist (Q 0).center (Q 1).center = 250 ∧
      ∃ μ ν : ProbabilityMeasure Plane,
        IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
        (μ : Measure Plane).support ⊆ (fun x : Plane => s • x) '' E ∧
        (ν : Measure Plane).support ⊆ (fun x : Plane => s • x) '' E ∧
        (μ : Measure Plane).support ⊆ (Q 0).carrier ∧
        (ν : Measure Plane).support ⊆ (Q 1).carrier ∧
        (μ : Measure Plane) (Q 0).carrierᶜ = 0 ∧ (ν : Measure Plane) (Q 1).carrierᶜ = 0 ∧
      ∃ C : ℝ, 0 < C ∧ BallBound μ (1+δ) C ∧ BallBound ν (1+δ) C ∧
      ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
        (∀ x ∈ (μ : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
        (∀ y ∈ (ν : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K) := by
  sorry

end PlanarFalconer

end OAI
end

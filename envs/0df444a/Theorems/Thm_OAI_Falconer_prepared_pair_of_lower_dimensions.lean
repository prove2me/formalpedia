-- Prove2me | Theorems.Thm_OAI_Falconer_prepared_pair_of_lower_dimensions
-- name    : OAI.Falconer.prepared_pair_of_lower_dimensions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:52:14.962691+00:00
-- url     : https://prove2.me/theorems/cd67680b-a3b3-4d44-9e5a-406e17bbbfe2
-- title:
--   OAI.Falconer.prepared_pair_of_lower_dimensions: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.prepared_pair_of_lower_dimensions` of [lean/OAI/MeasureTheory/Falconer/Estimates/StartingDescent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/StartingDescent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem prepared_pair_of_lower_dimensions
--       (hFrostman : PublishedFrostmanAboveHalf)
--       (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
--       (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
--       {d : ℕ}
--       (hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
--         (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
--       (hd : 2 ≤ d) (E : Set (Space d)) (hE : IsCompact E)
--       (hDim : (d:ℝ≥0∞)/2 < dimH E) {ε : ℝ} (hε : 0 < ε) :
--       0 < volume (distanceSet E) ∨ Nonempty (PreparedOriginalPair E ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.Space` and `OAI.Falconer.distanceSet` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedFiniteLoomisWhitney` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.PreparedOriginalPair`, `OAI.Falconer.PublishedFrostmanAboveHalf`, `OAI.Falconer.PublishedHeavyHyperplanes`, `OAI.Falconer.PublishedPlanarFurstenberg` and `OAI.Falconer.PublishedRadialMoment` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI_Falconer_mainTarget_of_five_published_inputs` and `OAI.Falconer.mainTarget_of_three_published_inputs` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/StartingDescent.lean (declaration OAI.Falconer.prepared_pair_of_lower_dimensions)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem prepared_pair_of_lower_dimensions
    (hFrostman : PublishedFrostmanAboveHalf)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {d : ℕ}
    (hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
      (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
    (hd : 2 ≤ d) (E : Set (Space d)) (hE : IsCompact E)
    (hDim : (d:ℝ≥0∞)/2 < dimH E) {ε : ℝ} (hε : 0 < ε) :
    0 < volume (distanceSet E) ∨ Nonempty (PreparedOriginalPair E ε) := by
  sorry

end Falconer

end OAI
end

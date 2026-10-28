-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_suffix_local_bins
-- name    : OAI.PlanarFalconer.uniform_actual_suffix_local_bins
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:57:48.176872+00:00
-- url     : https://prove2.me/theorems/a374464d-8d76-4aa0-8eab-d051699f51f9
-- title:
--   OAI.PlanarFalconer.uniform_actual_suffix_local_bins: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_suffix_local_bins` of [lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/ActualSuffixLocalBins.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/ActualSuffixLocalBins.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem uniform_actual_suffix_local_bins {sig : ℝ} (hsig : 0 < sig)
--       {J : ℕ} (hJ : 0 < J) :
--       ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
--         N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
--         ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
--         d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
--         let p := policyDepth (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
--         d.a+d.t < 2*p → ∀ c ∈ d.suffixRetained p,
--         (binL2Norm (d.suffixData c).distance d.width)^2 ≤
--           (((bandOffsets 3).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^d.N)^
--             (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
--               2000*(d.lam+sig)+12*d.lam))) * (d.suffixFullDistance c univ)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.bandOffsets`, `OAI.PlanarFalconer.binL2Norm`, `OAI.PlanarFalconer.height`, `OAI.PlanarFalconer.policyDepth`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.StronglySeparated`, `OAI.PlanarFalconer.PositiveDistanceData.distance`, `OAI.PlanarFalconer.PositiveDistanceData.suffixData`, `OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance`, `OAI.PlanarFalconer.PositiveDistanceData.suffixRetained` and `OAI.PlanarFalconer.PositiveDistanceData.width` (definitions bundle `OAIQ038F000` of this split).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.source_positive_distance_suffix` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/ActualSuffixLocalBins.lean (declaration OAI.PlanarFalconer.uniform_actual_suffix_local_bins)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ038F000

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_actual_suffix_local_bins {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let p := policyDepth (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
      d.a+d.t < 2*p → ∀ c ∈ d.suffixRetained p,
      (binL2Norm (d.suffixData c).distance d.width)^2 ≤
        (((bandOffsets 3).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^d.N)^
          (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
            2000*(d.lam+sig)+12*d.lam))) * (d.suffixFullDistance c univ)^2 := by
  sorry

end PlanarFalconer

end OAI
end

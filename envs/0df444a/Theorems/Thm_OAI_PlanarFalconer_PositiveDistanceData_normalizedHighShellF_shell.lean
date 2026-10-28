-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_normalizedHighShellF_shell
-- name    : OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_shell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:59:20.926277+00:00
-- url     : https://prove2.me/theorems/f3c7e7ad-a5d8-4982-9c0e-876cfa6c5616
-- title:
--   OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_shell: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_shell` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellMainEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellMainEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.PositiveDistanceData`, with `open Set MeasureTheory Filter`):
--
--   ```lean
--   theorem normalizedHighShellF_shell (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
--       (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (hsig : 0 ≤ d.sig)
--       (hq : 0 < d.q) (hqs : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
--       {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (n : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
--       (hB : ∀ j ∈ Finset.range (n+1),
--         ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
--         (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖d.inversePhasedForm b.2 ξ r‖^2) ≤ B) :
--       (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖d.normalizedHighShellF n v r‖^2) ≤
--         2*(2:ℝ)^(v-d.a) *
--           (∑ j ∈ Finset.range (n+1), spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
--             (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)^2*B
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PairMaskIndex`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.inverseLeibnizTerms`, `OAI.PlanarFalconer.pairMaskIndices`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.StronglySeparated`, `OAI.PlanarFalconer.PositiveDistanceData.inverseDescriptorList`, `OAI.PlanarFalconer.PositiveDistanceData.inversePhasedForm` and `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.spatialLeibnizCost` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellMainEnergy.lean (declaration OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_shell)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

theorem normalizedHighShellF_shell (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (hsig : 0 ≤ d.sig)
    (hq : 0 < d.q) (hqs : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
    {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (n : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖d.inversePhasedForm b.2 ξ r‖^2) ≤ B) :
    (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖d.normalizedHighShellF n v r‖^2) ≤
      2*(2:ℝ)^(v-d.a) *
        (∑ j ∈ Finset.range (n+1), spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
          (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)^2*B := by
  sorry

end PositiveDistanceData

end PlanarFalconer

end OAI
end

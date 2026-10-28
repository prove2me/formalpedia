-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_inverseOrderForm_shell
-- name    : OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm_shell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:52:41.761143+00:00
-- url     : https://prove2.me/theorems/e18cd145-4f1d-4089-800f-ff0242f180eb
-- title:
--   OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm_shell: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm_shell` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellOrderForm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellOrderForm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.PositiveDistanceData`, with `open Set MeasureTheory Filter`):
--
--   ```lean
--   theorem inverseOrderForm_shell (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
--       (hQ : 0 < d.Q.side) (hsig : 0 ≤ d.sig) (hq : 0 < d.q)
--       (hqs : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
--       {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (j : ℕ)
--       (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ} (_hB0 : 0 ≤ B)
--       (hB : ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
--         (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
--       (∫ r, ‖d.inverseOrderForm j v r‖^2 ∂μ) ≤
--         (spatialFourierCost 96 2004 (by norm_num) (by norm_num) j *
--           ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b => ‖b.1‖)).sum)^2*B
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PairMaskIndex`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.inverseLeibnizTerms`, `OAI.PlanarFalconer.pairMaskIndices`, `OAI.PlanarFalconer.spatialFourierCost`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.inverseDescriptorList`, `OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm` and `OAI.PlanarFalconer.PositiveDistanceData.inversePhasedForm` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_shell` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellOrderForm.lean (declaration OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm_shell)

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
open Set MeasureTheory Filter
namespace PositiveDistanceData

theorem inverseOrderForm_shell (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hsig : 0 ≤ d.sig) (hq : 0 < d.q)
    (hqs : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
    {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (j : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
      (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
    (∫ r, ‖d.inverseOrderForm j v r‖^2 ∂μ) ≤
      (spatialFourierCost 96 2004 (by norm_num) (by norm_num) j *
        ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b => ‖b.1‖)).sum)^2*B := by
  sorry

end PositiveDistanceData

end PlanarFalconer

end OAI
end

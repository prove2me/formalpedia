-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_RootShellData_inverseOrderForm_shell
-- name    : OAI.PlanarFalconer.RootShellData.inverseOrderForm_shell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:54:59.448321+00:00
-- url     : https://prove2.me/theorems/a3069597-86cf-46fa-84ae-acf877b4dc5a
-- title:
--   OAI.PlanarFalconer.RootShellData.inverseOrderForm_shell: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.RootShellData.inverseOrderForm_shell` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/RootShellOrder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/RootShellOrder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.RootShellData`, with `open Set MeasureTheory Filter`):
--
--   ```lean
--   theorem inverseOrderForm_shell (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
--       (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (hsig : 0 ≤ d.sig)
--       (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
--       (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2) (j : ℕ)
--       (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ} (_hB0 : 0 ≤ B)
--       (hB : ∀ b ∈ inverseLeibnizTerms j (d.indices), ∀ ξ,
--         (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
--       (∫ r, ‖d.inverseOrderForm δ L hδ hL j r‖^2 ∂μ) ≤
--         (spatialFourierCost δ L hδ hL j *
--           ((inverseLeibnizTerms j (d.indices)).map (fun b => ‖b.1‖)).sum)^2*B
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RootMaskIndex`, `OAI.PlanarFalconer.RootShellData`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.inverseLeibnizTerms`, `OAI.PlanarFalconer.spatialFourierCost`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.RootEndpointData`, `OAI.PlanarFalconer.RootShellData.indices`, `OAI.PlanarFalconer.RootShellData.inverseOrderForm` and `OAI.PlanarFalconer.RootShellData.inversePhasedForm` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.RootShellData.mainF_shell` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/RootShellOrder.lean (declaration OAI.PlanarFalconer.RootShellData.inverseOrderForm_shell)

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
namespace RootShellData

theorem inverseOrderForm_shell (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (hsig : 0 ≤ d.sig)
    (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
    (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2) (j : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ b ∈ inverseLeibnizTerms j (d.indices), ∀ ξ,
      (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
    (∫ r, ‖d.inverseOrderForm δ L hδ hL j r‖^2 ∂μ) ≤
      (spatialFourierCost δ L hδ hL j *
        ((inverseLeibnizTerms j (d.indices)).map (fun b => ‖b.1‖)).sum)^2*B := by
  sorry

end RootShellData

end PlanarFalconer

end OAI
end

-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_RootShellData_mainF_shell
-- name    : OAI.PlanarFalconer.RootShellData.mainF_shell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:54:19.094825+00:00
-- url     : https://prove2.me/theorems/05c3653f-b37a-4ac8-b088-693aa1adbc24
-- title:
--   OAI.PlanarFalconer.RootShellData.mainF_shell: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.RootShellData.mainF_shell` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/RootShellMain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/RootShellMain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.RootShellData`, with `open Set MeasureTheory Filter`):
--
--   ```lean
--   theorem mainF_shell (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
--       [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
--       (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (hsig : 0 ≤ d.sig)
--       (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
--       (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2)
--       (hcarry₁ : ∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) (hcarry₂ : ∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier)
--       (hsep : ∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) (n : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
--       (hB : ∀ j ∈ Finset.range (n+1),
--         ∀ b ∈ inverseLeibnizTerms j (d.indices), ∀ ξ,
--         (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.inversePhasedForm b.2 ξ r‖^2) ≤ B) :
--       (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.mainF n r‖^2) ≤
--         2*(2:ℝ)^((d.N:ℝ)) *
--           (∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j)^2*B
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RootMaskIndex`, `OAI.PlanarFalconer.RootShellData`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.inverseLeibnizTerms`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.RootEndpointData`, `OAI.PlanarFalconer.RootShellData.cost`, `OAI.PlanarFalconer.RootShellData.indices`, `OAI.PlanarFalconer.RootShellData.inversePhasedForm` and `OAI.PlanarFalconer.RootShellData.mainF` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.RootShellData.uniform_parent_bound` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/RootShellMain.lean (declaration OAI.PlanarFalconer.RootShellData.mainF_shell)

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

theorem mainF_shell (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (hsig : 0 ≤ d.sig)
    (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
    (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2)
    (hcarry₁ : ∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) (hcarry₂ : ∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier)
    (hsep : ∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) (n : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (d.indices), ∀ ξ,
      (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.inversePhasedForm b.2 ξ r‖^2) ≤ B) :
    (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.mainF n r‖^2) ≤
      2*(2:ℝ)^((d.N:ℝ)) *
        (∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j)^2*B := by
  sorry

end RootShellData

end PlanarFalconer

end OAI
end

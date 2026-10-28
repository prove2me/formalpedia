-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_comparable_shell_rebin
-- name    : OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:01:23.476002+00:00
-- url     : https://prove2.me/theorems/0c9ead3b-8f4c-4677-97a0-862959c0d2b0
-- title:
--   OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/ActualComparableShellRebin.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/ActualComparableShellRebin.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ENNReal ContDiff`):
--
--   ```lean
--   theorem uniform_actual_comparable_shell_rebin {Ψ : ℝ → ℝ}
--       (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
--       {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
--       ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
--       ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
--       ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
--       (∀ l, ρ l (Q l).carrierᶜ = 0) →
--       ∀ (m : Fin 2 → ℝ → ℝ) (q a₀ t₀ a d n v : ℕ),
--       0 < q → a₀ ≤ a+n → v ≤ t₀ → v ≤ N →
--       ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
--       (∀ l, remainingPolicyDescriptors (fun t => m l t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
--       (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
--       ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
--       ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
--       ∀ (lam : Fin 2 → ℝ) (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
--       (∀ l x, ‖hsp l x‖ ≤ 1) →
--       ∀ A B : CellPath, A.length = a → B.length = a →
--       let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l)
--         N (lam l) sig J (i l) (hsp l)
--       let good := fun l => positiveDistanceGoodSet (Q l) (ρ l) (m l) N q (a+n) v (lam l) sig J (i l+1)
--       ‖∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
--         ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
--           if ¬ angularNear (Q 0) (Q 1) (a+d) row col then
--             ∫ x in angularLengthShell (a+n), angularStationarySpatialKernel (β 0) (β 1) o v Ψ x
--               ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
--           else 0‖ₑ ≤
--       (ENNReal.ofReal H * ENNReal.ofReal ((2:ℝ)^(-((v:ℝ)-(a+n:ℕ))))) *
--         ∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
--           ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
--             if angularSeparated (Q 0) (Q 1) (a+n) row col then
--               ∫⁻ x in angularLengthShell (a+n),
--                 (fourPairGood (good 0) (good 1)).indicator (distanceDifferenceKernel v) x
--                   ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
--             else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.angularFourCellMeasure`, `OAI.PlanarFalconer.angularLengthShell`, `OAI.PlanarFalconer.angularNear`, `OAI.PlanarFalconer.angularSeparated`, `OAI.PlanarFalconer.angularStationarySpatialKernel`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.inheritedCircleSymbol`, `OAI.PlanarFalconer.positiveDistanceGoodSet`, `OAI.PlanarFalconer.remainingPolicyDescriptors`, `OAI.PlanarFalconer.sourceProductVertices` and `OAI.PlanarFalconer.DyadicSquare.carrier` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.distanceDifferenceKernel` and `OAI.PlanarFalconer.fourPairGood` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_far_source_equation24` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/ActualComparableShellRebin.lean (declaration OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_comparable_shell_rebin {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : Fin 2 → ℝ → ℝ) (q a₀ t₀ a d n v : ℕ),
    0 < q → a₀ ≤ a+n → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m l t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (lam : Fin 2 → ℝ) (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l)
      N (lam l) sig J (i l) (hsp l)
    let good := fun l => positiveDistanceGoodSet (Q l) (ρ l) (m l) N q (a+n) v (lam l) sig J (i l+1)
    ‖∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
      ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
        if ¬ angularNear (Q 0) (Q 1) (a+d) row col then
          ∫ x in angularLengthShell (a+n), angularStationarySpatialKernel (β 0) (β 1) o v Ψ x
            ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
        else 0‖ₑ ≤
    (ENNReal.ofReal H * ENNReal.ofReal ((2:ℝ)^(-((v:ℝ)-(a+n:ℕ))))) *
      ∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
        ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
          if angularSeparated (Q 0) (Q 1) (a+n) row col then
            ∫⁻ x in angularLengthShell (a+n),
              (fourPairGood (good 0) (good 1)).indicator (distanceDifferenceKernel v) x
                ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
          else 0 := by
  sorry

end PlanarFalconer

end OAI
end

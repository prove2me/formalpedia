-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_four_approximant_good
-- name    : OAI.PlanarFalconer.uniform_actual_four_approximant_good
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:57:03.141524+00:00
-- url     : https://prove2.me/theorems/28d69818-1852-4768-bc5d-ac2c7871fe91
-- title:
--   OAI.PlanarFalconer.uniform_actual_four_approximant_good: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_four_approximant_good` of [lean/OAI/MeasureTheory/Falconer/Falconer/Angular/ActualFourStationarySupport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/ActualFourStationarySupport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`):
--
--   ```lean
--   theorem uniform_actual_four_approximant_good {sig : ℝ} (hsig : 0 < sig)
--       {J : ℕ} (hJ : 0 < J) :
--       ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
--       ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
--       (∀ l, ρ l (Q l).carrierᶜ = 0) →
--       ∀ (m : Fin 2 → ℝ → ℝ) (q a₀ t₀ a b v : ℕ), 0 < q → a₀ ≤ b → v ≤ t₀ →
--       a ≤ b → v ≤ N →
--       ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
--       (∀ l, remainingPolicyDescriptors (fun n => m l n-(n:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
--       ∀ (lam : Fin 2 → ℝ) (i : Fin 2 → ℕ) (h : Fin 2 → Plane → ℂ) (X : Fin 4 → Set Plane),
--       let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l) N (lam l) sig J (i l) (h l)
--       ∀ᵐ x ∂Measure.pi (fun j => (![ρ 0,ρ 0,ρ 1,ρ 1] j).restrict (X j)),
--       ∀ (n : ℕ) (w : ℝ) (Ψ : ℝ → ℝ), (∀ t, Ψ t ≠ 0 → 0 < t) →
--       x 0 ≠ x 1 → x 2 ≠ x 3 → angularStationarySpatialKernel (β 0) (β 1) n w Ψ x ≠ 0 →
--       (x 0,x 1) ∈ positiveDistanceGoodSet (Q 0) (ρ 0) (m 0) N q b v (lam 0) sig J (i 0+1) ∧
--       (x 2,x 3) ∈ positiveDistanceGoodSet (Q 1) (ρ 1) (m 1) N q b v (lam 1) sig J (i 1+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.angularStationarySpatialKernel`, `OAI.PlanarFalconer.inheritedCircleSymbol`, `OAI.PlanarFalconer.positiveDistanceGoodSet`, `OAI.PlanarFalconer.remainingPolicyDescriptors` and `OAI.PlanarFalconer.DyadicSquare.carrier` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/ActualFourStationarySupport.lean (declaration OAI.PlanarFalconer.uniform_actual_four_approximant_good)

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

theorem uniform_actual_four_approximant_good {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : Fin 2 → ℝ → ℝ) (q a₀ t₀ a b v : ℕ), 0 < q → a₀ ≤ b → v ≤ t₀ →
    a ≤ b → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun n => m l n-(n:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    ∀ (lam : Fin 2 → ℝ) (i : Fin 2 → ℕ) (h : Fin 2 → Plane → ℂ) (X : Fin 4 → Set Plane),
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l) N (lam l) sig J (i l) (h l)
    ∀ᵐ x ∂Measure.pi (fun j => (![ρ 0,ρ 0,ρ 1,ρ 1] j).restrict (X j)),
    ∀ (n : ℕ) (w : ℝ) (Ψ : ℝ → ℝ), (∀ t, Ψ t ≠ 0 → 0 < t) →
    x 0 ≠ x 1 → x 2 ≠ x 3 → angularStationarySpatialKernel (β 0) (β 1) n w Ψ x ≠ 0 →
    (x 0,x 1) ∈ positiveDistanceGoodSet (Q 0) (ρ 0) (m 0) N q b v (lam 0) sig J (i 0+1) ∧
    (x 2,x 3) ∈ positiveDistanceGoodSet (Q 1) (ρ 1) (m 1) N q b v (lam 1) sig J (i 1+1) := by
  sorry

end PlanarFalconer

end OAI
end

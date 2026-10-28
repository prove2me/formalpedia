-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_single_stationary_kernel
-- name    : OAI.PlanarFalconer.uniform_actual_single_stationary_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:57:58.644596+00:00
-- url     : https://prove2.me/theorems/45c27e7a-4c21-44d8-a051-31bfbb0ee882
-- title:
--   OAI.PlanarFalconer.uniform_actual_single_stationary_kernel: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_single_stationary_kernel` of [lean/OAI/MeasureTheory/Falconer/Falconer/Angular/ActualSingleStationaryKernel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/ActualSingleStationaryKernel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff ComplexConjugate`):
--
--   ```lean
--   theorem uniform_actual_single_stationary_kernel {Ψ : ℝ → ℝ}
--       (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
--       {sig : ℝ} (hsig : 0 < sig) (K n q : ℕ) :
--       ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
--       ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
--       ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
--       (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
--       ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
--       ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
--       ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
--       (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ) (x y : Fin 2 → Plane),
--       (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
--       ∀ v : ℝ, 0 < ‖x 0-y 0‖ → 2*‖x 1-y 1‖ ≤ ‖x 0-y 0‖ →
--       sourceSymbolScale N sig L^2 ≤ (2:ℝ)^v*‖x 0-y 0‖ →
--       let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
--         N (lam l) sig (J l) (i l) (hsp l)
--       ‖angularSingleStationaryKernel (β 0) (β 1) n v Ψ ![x 0,y 0,x 1,y 1]‖ ≤
--         H*((2:ℝ)^v*‖x 0-y 0‖)^(-1/2:ℝ)/((2:ℝ)^v*‖x 0-y 0‖/2)^q
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.angularSingleStationaryKernel`, `OAI.PlanarFalconer.descriptorLength` and `OAI.PlanarFalconer.inheritedCircleSymbol` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.sourceSymbolScale` (definitions bundle `OAIQ038F001` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_noncomparable_radial_either` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/ActualSingleStationaryKernel.lean (declaration OAI.PlanarFalconer.uniform_actual_single_stationary_kernel)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000
import Definitions.Def_OAIQ038F001

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_actual_single_stationary_kernel {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K n q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ) (x y : Fin 2 → Plane),
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v : ℝ, 0 < ‖x 0-y 0‖ → 2*‖x 1-y 1‖ ≤ ‖x 0-y 0‖ →
    sourceSymbolScale N sig L^2 ≤ (2:ℝ)^v*‖x 0-y 0‖ →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    ‖angularSingleStationaryKernel (β 0) (β 1) n v Ψ ![x 0,y 0,x 1,y 1]‖ ≤
      H*((2:ℝ)^v*‖x 0-y 0‖)^(-1/2:ℝ)/((2:ℝ)^v*‖x 0-y 0‖/2)^q := by
  sorry

end PlanarFalconer

end OAI
end

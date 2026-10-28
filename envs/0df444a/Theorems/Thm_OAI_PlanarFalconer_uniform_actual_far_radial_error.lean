-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_far_radial_error
-- name    : OAI.PlanarFalconer.uniform_actual_far_radial_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:56:39.203486+00:00
-- url     : https://prove2.me/theorems/6f3109a8-c7a1-4599-9de1-acd320c55d1b
-- title:
--   OAI.PlanarFalconer.uniform_actual_far_radial_error: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_far_radial_error` of [lean/OAI/MeasureTheory/Falconer/Falconer/Radial/ActualFarRadialError.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Radial/ActualFarRadialError.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ComplexConjugate`):
--
--   ```lean
--   theorem uniform_actual_far_radial_error {sig T : ℝ} (hsig : 0 < sig) (K : ℕ)
--       {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
--       (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
--       {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
--       ∃ n N₀ : ℕ, ∀ N ≥ N₀,
--       ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
--       ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
--       (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
--       ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
--       ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
--       ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
--       (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
--       (∀ l, Measurable (hsp l)) → ∀ x y : Fin 2 → Plane,
--       (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
--       ∀ v h L₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
--       (∀ l, 4*(2:ℝ)^(-h) ≤ ‖x l-y l‖) → ∀ θ : Fin 2 → ℝ,
--       (∀ l, x l-y l = ‖x l-y l‖ • sourceDirection (θ l)) →
--       let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
--         N (lam l) sig (J l) (i l) (hsp l)
--       let E := fun l r => fullCircleStationaryExpansion (r*‖x l-y l‖)
--         (fun t => β l (x l) (sourceUnitDirection (t+θ l))*
--           conj (β l (y l) (sourceUnitDirection (t+θ l)))) n
--       ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
--           (angularPairCircleIntegral (β 0) (x 0) (y 0) r *
--            angularPairCircleIntegral (β 1) (x 1) (y 1) r)) -
--         ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (E 0 r*E 1 r))‖ ≤
--         ((2:ℝ)^N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.angularPairCircleIntegral`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.fullCircleStationaryExpansion`, `OAI.PlanarFalconer.inheritedCircleSymbol`, `OAI.PlanarFalconer.sourceDirection` and `OAI.PlanarFalconer.sourceUnitDirection` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_comparable_far_error` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Radial/ActualFarRadialError.lean (declaration OAI.PlanarFalconer.uniform_actual_far_radial_error)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem uniform_actual_far_radial_error {sig T : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → ∀ x y : Fin 2 → Plane,
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v h L₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    (∀ l, 4*(2:ℝ)^(-h) ≤ ‖x l-y l‖) → ∀ θ : Fin 2 → ℝ,
    (∀ l, x l-y l = ‖x l-y l‖ • sourceDirection (θ l)) →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    let E := fun l r => fullCircleStationaryExpansion (r*‖x l-y l‖)
      (fun t => β l (x l) (sourceUnitDirection (t+θ l))*
        conj (β l (y l) (sourceUnitDirection (t+θ l)))) n
    ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
        (angularPairCircleIntegral (β 0) (x 0) (y 0) r *
         angularPairCircleIntegral (β 1) (x 1) (y 1) r)) -
      ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (E 0 r*E 1 r))‖ ≤
      ((2:ℝ)^N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end

-- Prove2me | Theorems.Thm_OAI_EditApproximation_list_band_computed_entropy_regret
-- name    : OAI.EditApproximation.list_band_computed_entropy_regret
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:17.416168+00:00
-- url     : https://prove2.me/theorems/f9f897c4-2015-434f-b590-f852dc625f8b
-- title:
--   OAI.EditApproximation.list_band_computed_entropy_regret: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.list_band_computed_entropy_regret` of [lean/OAI/Combinatorics/EditApproximation/Geometry/ListBandRegret.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/ListBandRegret.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset`):
--
--   ```lean
--   theorem list_band_computed_entropy_regret {β σ : Type*} [Fintype β] [Nonempty β]
--       [DecidableEq β] [DecidableEq σ] (band : List (β → σ)) (hband : band ≠ [])
--       (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
--       (S H : ℕ) (η κ : ℚ) (rangeBound : ℝ)
--       (gain decrement : ℕ → β × σ → ℚ) {comparison : β → σ} (hc : comparison ∈ band)
--       (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
--       (hηrange : (η : ℝ) * rangeBound ≤ (κ : ℝ))
--       (hdecrementNonneg : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset, (0 : ℝ) ≤ decrement t i)
--       (hrange : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset, ∀ j ∈ bandCoordinates band.toFinset,
--         i.1 = j.1 → |(decrement t i : ℝ) - decrement t j| ≤ rangeBound)
--       (hdecrement : ∀ i ∈ bandCoordinates band.toFinset, ∑ t ∈ range S, (decrement t i : ℝ) ≤ 1)
--       (hgain : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset,
--         -1 ≤ (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ∧
--           (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ≤ 0) :
--       (∑ t ∈ range S, ∑ i ∈ bandCoordinates band.toFinset,
--           ((gain t i : ℝ) + decrement t i) * (actionVector mass comparison i : ℝ)) -
--           Real.log (bandCoordinates band.toFinset).card / (η : ℝ) - 2 * (κ : ℝ) - (S : ℝ) / (H : ℝ) ^ 3 ≤
--         ∑ t ∈ range S, ∑ i ∈ bandCoordinates band.toFinset,
--           ((gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i) *
--             (computedOnlineVector (bandCoordinates band.toFinset) (band.map (actionVector mass))
--               η κ gain decrement H t i : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedOnlineVector` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.actionVector` and `OAI.EditApproximation.bandCoordinates` (the published bundle `Def_EditApproxScheme_02`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalBand_prefix_expected_regret` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/ListBandRegret.lean (declaration OAI.EditApproximation.list_band_computed_entropy_regret)

import Mathlib
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_OAIQ361V3Ea001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset

theorem list_band_computed_entropy_regret {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : List (β → σ)) (hband : band ≠ [])
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (S H : ℕ) (η κ : ℚ) (rangeBound : ℝ)
    (gain decrement : ℕ → β × σ → ℚ) {comparison : β → σ} (hc : comparison ∈ band)
    (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) * rangeBound ≤ (κ : ℝ))
    (hdecrementNonneg : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset, (0 : ℝ) ≤ decrement t i)
    (hrange : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset, ∀ j ∈ bandCoordinates band.toFinset,
      i.1 = j.1 → |(decrement t i : ℝ) - decrement t j| ≤ rangeBound)
    (hdecrement : ∀ i ∈ bandCoordinates band.toFinset, ∑ t ∈ range S, (decrement t i : ℝ) ≤ 1)
    (hgain : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset,
      -1 ≤ (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ∧
        (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ≤ 0) :
    (∑ t ∈ range S, ∑ i ∈ bandCoordinates band.toFinset,
        ((gain t i : ℝ) + decrement t i) * (actionVector mass comparison i : ℝ)) -
        Real.log (bandCoordinates band.toFinset).card / (η : ℝ) - 2 * (κ : ℝ) - (S : ℝ) / (H : ℝ) ^ 3 ≤
      ∑ t ∈ range S, ∑ i ∈ bandCoordinates band.toFinset,
        ((gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i) *
          (computedOnlineVector (bandCoordinates band.toFinset) (band.map (actionVector mass))
            η κ gain decrement H t i : ℝ) := by
  sorry

end EditApproximation

end OAI
end

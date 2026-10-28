-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_root_weighted_inverse
-- name    : OAI.PlanarFalconer.uniform_root_weighted_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:03:26.493772+00:00
-- url     : https://prove2.me/theorems/8a658f18-4328-4282-8cd7-8fb6bc2713b9
-- title:
--   OAI.PlanarFalconer.uniform_root_weighted_inverse: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_root_weighted_inverse` of [lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/RootWeightedInverse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/RootWeightedInverse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`):
--
--   ```lean
--   theorem uniform_root_weighted_inverse {sig δ T : ℝ}
--       (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) :
--       ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
--       0 < d.Q.side → 0 < e.Q.side →
--       d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
--       (∀ b ∈ d.S, descriptorLength b ≤ N/2) →
--       (∀ b ∈ e.S, descriptorLength b ≤ N/2) →
--       ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
--       ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
--       ∀ r : ℝ, (2:ℝ)^((N:ℝ)-1) ≤ r →
--       ∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y →
--       ‖(rootSpatialWeight d e N sig (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
--         (((dist x y)^(-(1/2:ℝ)):ℝ):ℂ) *
--           sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
--             (rootPairSymbol d e N sig (x,y))‖ ≤ ((2:ℝ)^N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RootEndpointData`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.rootSpatialWeight`, `OAI.PlanarFalconer.sourceConeCircle`, `OAI.PlanarFalconer.sourceParentAxis`, `OAI.PlanarFalconer.DyadicSquare.carrier` and `OAI.PlanarFalconer.DyadicSquare.center` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.rootPairSymbol` and `OAI.PlanarFalconer.sourceInverseCircleIntegral` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_root_fourier_error` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/RootWeightedInverse.lean (declaration OAI.PlanarFalconer.uniform_root_weighted_inverse)

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
open Set MeasureTheory

theorem uniform_root_weighted_inverse {sig δ T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    0 < d.Q.side → 0 < e.Q.side →
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    (∀ b ∈ d.S, descriptorLength b ≤ N/2) →
    (∀ b ∈ e.S, descriptorLength b ≤ N/2) →
    ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
    ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
    ∀ r : ℝ, (2:ℝ)^((N:ℝ)-1) ≤ r →
    ∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y →
    ‖(rootSpatialWeight d e N sig (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
      (((dist x y)^(-(1/2:ℝ)):ℝ):ℂ) *
        sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
          (rootPairSymbol d e N sig (x,y))‖ ≤ ((2:ℝ)^N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end

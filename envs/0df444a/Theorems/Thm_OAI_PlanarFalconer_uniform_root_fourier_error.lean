-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_root_fourier_error
-- name    : OAI.PlanarFalconer.uniform_root_fourier_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:58:38.995992+00:00
-- url     : https://prove2.me/theorems/4b2bd750-8c2d-479b-876e-9a85e471fed4
-- title:
--   OAI.PlanarFalconer.uniform_root_fourier_error: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_root_fourier_error` of [lean/OAI/MeasureTheory/Falconer/Falconer/Fourier/RootUniformFourier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Fourier/RootUniformFourier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory Filter`):
--
--   ```lean
--   theorem uniform_root_fourier_error {sig δ T : ℝ}
--       (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) :
--       ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
--       ∀ [IsProbabilityMeasure d.ρ] [IsProbabilityMeasure e.ρ],
--       0 < d.Q.side → 0 < e.Q.side →
--       d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
--       (∀ b ∈ d.S, descriptorLength b ≤ N/2) →
--       (∀ b ∈ e.S, descriptorLength b ≤ N/2) →
--       ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
--       (∀ᵐ x ∂d.ρ, x ∈ U.carrier) → (∀ᵐ y ∂e.ρ, y ∈ V.carrier) →
--       (∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y) →
--       ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
--       ∀ r : ℝ, (2:ℝ)^((N:ℝ)-1) ≤ r →
--       Integrable (rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)))
--         (d.ρ.prod e.ρ) ∧
--       ‖charFun (rootWeightedDistance d e N sig) r - rootNormalizedF d e N sig n U V r‖ ≤
--         ((2:ℝ)^N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RootEndpointData`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.rootNormalizedF`, `OAI.PlanarFalconer.rootNormalizedKernel`, `OAI.PlanarFalconer.rootWeightedDistance`, `OAI.PlanarFalconer.sourceConeCircle`, `OAI.PlanarFalconer.sourceParentAxis`, `OAI.PlanarFalconer.DyadicSquare.carrier` and `OAI.PlanarFalconer.DyadicSquare.center` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.RootShellData.uniform_parent_bound` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Fourier/RootUniformFourier.lean (declaration OAI.PlanarFalconer.uniform_root_fourier_error)

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

theorem uniform_root_fourier_error {sig δ T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    ∀ [IsProbabilityMeasure d.ρ] [IsProbabilityMeasure e.ρ],
    0 < d.Q.side → 0 < e.Q.side →
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    (∀ b ∈ d.S, descriptorLength b ≤ N/2) →
    (∀ b ∈ e.S, descriptorLength b ≤ N/2) →
    ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
    (∀ᵐ x ∂d.ρ, x ∈ U.carrier) → (∀ᵐ y ∂e.ρ, y ∈ V.carrier) →
    (∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y) →
    ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
    ∀ r : ℝ, (2:ℝ)^((N:ℝ)-1) ≤ r →
    Integrable (rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)))
      (d.ρ.prod e.ρ) ∧
    ‖charFun (rootWeightedDistance d e N sig) r - rootNormalizedF d e N sig n U V r‖ ≤
      ((2:ℝ)^N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end

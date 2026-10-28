-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_RootShellData_uniform_parent_bound
-- name    : OAI.PlanarFalconer.RootShellData.uniform_parent_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:54:20.803989+00:00
-- url     : https://prove2.me/theorems/4b2656b3-3827-4935-98f3-ca17b2674d23
-- title:
--   OAI.PlanarFalconer.RootShellData.uniform_parent_bound: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.RootShellData.uniform_parent_bound` of [lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/RootEquation21.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/RootEquation21.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.RootShellData`, with `open Set MeasureTheory Filter`):
--
--   ```lean
--   theorem uniform_parent_bound {sig δ L eps T : ℝ}
--       (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) (hL : 0 < L) (heps : 0 < eps) :
--       ∃ n N₀ : ℕ, ∀ d : RootShellData,
--       ∀ [IsProbabilityMeasure d.left.ρ] [IsProbabilityMeasure d.right.ρ],
--       N₀ ≤ d.N → d.sig = sig → 0 < d.left.Q.side → 0 < d.right.Q.side →
--       d.left.S.card ≤ (d.N+1)^3+1 → d.right.S.card ≤ (d.N+1)^3+1 →
--       (∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2) →
--       (∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2) →
--       0 < d.U.side → 0 < d.V.side →
--       (∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) → (∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier) →
--       (∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) →
--       ∀ s : ℝ, d.U.side ≤ s → d.V.side ≤ s → 100*s ≤ dist d.U.center d.V.center →
--       ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
--       (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
--       ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) → (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
--       ∀ H : ℝ, 0 ≤ H →
--       (∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
--         (d.inversePhasedHF d.N Ψ b.2 ξ).toReal ≤ H) →
--       (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
--         ((2:ℝ)^d.N)^eps*H+((2:ℝ)^d.N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RootMaskIndex`, `OAI.PlanarFalconer.RootShellData`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.inverseLeibnizTerms`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare.center`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.RootEndpointData`, `OAI.PlanarFalconer.RootShellData.indices`, `OAI.PlanarFalconer.RootShellData.inversePhasedHF` and `OAI.PlanarFalconer.RootShellData.measure` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_independent_class_equation27` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/RootEquation21.lean (declaration OAI.PlanarFalconer.RootShellData.uniform_parent_bound)

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

theorem uniform_parent_bound {sig δ L eps T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) (hL : 0 < L) (heps : 0 < eps) :
    ∃ n N₀ : ℕ, ∀ d : RootShellData,
    ∀ [IsProbabilityMeasure d.left.ρ] [IsProbabilityMeasure d.right.ρ],
    N₀ ≤ d.N → d.sig = sig → 0 < d.left.Q.side → 0 < d.right.Q.side →
    d.left.S.card ≤ (d.N+1)^3+1 → d.right.S.card ≤ (d.N+1)^3+1 →
    (∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2) →
    (∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2) →
    0 < d.U.side → 0 < d.V.side →
    (∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) → (∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier) →
    (∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) →
    ∀ s : ℝ, d.U.side ≤ s → d.V.side ≤ s → 100*s ≤ dist d.U.center d.V.center →
    ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
    (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
    ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) → (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
    ∀ H : ℝ, 0 ≤ H →
    (∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
      (d.inversePhasedHF d.N Ψ b.2 ξ).toReal ≤ H) →
    (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
      ((2:ℝ)^d.N)^eps*H+((2:ℝ)^d.N)^(-T) := by
  sorry

end RootShellData

end PlanarFalconer

end OAI
end

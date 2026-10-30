-- Prove2me | Theorems.Thm_OAI_Falconer_exists_policy_scalar_conversion
-- name    : OAI.Falconer.exists_policy_scalar_conversion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:50:31.355021+00:00
-- url     : https://prove2.me/theorems/daa99f86-0ad5-4224-a030-73516a3302b1
-- title:
--   OAI.Falconer.exists_policy_scalar_conversion: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.exists_policy_scalar_conversion` of [lean/OAI/MeasureTheory/Falconer/Estimates/PolicyScalarConversion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/PolicyScalarConversion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open PlanarFalconer (PolicyDescriptor)`):
--
--   ```lean
--   theorem exists_policy_scalar_conversion
--       (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
--       (m : ℕ) {σ ε : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
--       (lam T δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
--       (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r)
--       (hzero : ∀ r ≤ 0, Ψ r = 0) (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
--       {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
--       (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
--       ∃ K : ℕ, minJet ≤ K ∧ ∀ L : ℕ, ∀ Z : ℝ, 0 < Z → ∃ N₀ : ℕ,
--         ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.Z = Z → N₀ ≤ P.N →
--         (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
--           dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
--         (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
--           (P.ρ.restrict (P.Q.descendant P.Y).carrier),
--           δ ≤ dist z.1 z.2*(2:ℝ)^P.a ∧ dist z.1 z.2*(2:ℝ)^P.a ≤ W) →
--         125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
--           ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
--         20*P.σ*(P.N:ℝ) ≤ (P.t:ℝ)-P.a →
--         (P.longest:ℝ) ≤ ((P.t:ℝ)-P.a)/2+P.σ*P.N →
--         ∀ w₀ : Sphere (m+3),
--         (2:ℝ)^(-(P.a:ℝ))*
--           (∫ r in Icc ((2:ℝ)^((P.t:ℝ)-1)) ((2:ℝ)^((P.t:ℝ)+1)),
--             ‖charFun (maskedCellDistance w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list
--               P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)) r‖^2) ≤
--         ((2:ℝ)^P.N)^ε*P.envelope K L Ψ+((2:ℝ)^P.N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.PolicyJetData`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.descriptorMaskRadius`, `OAI.Falconer.maskedCellDistance`, `OAI.Falconer.DyadicCube.carrier`, `OAI.Falconer.DyadicCube.center`, `OAI.Falconer.DyadicCube.descendant`, `OAI.Falconer.DyadicCube`, `OAI.Falconer.PolicyJetData.envelope`, `OAI.Falconer.PolicyJetData.list` and `OAI.Falconer.PolicyJetData.longest` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface` and `OAI.Falconer.PublishedQuadraticStationary` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.exists_policy_prefix_common_budgets` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/PolicyScalarConversion.lean (declaration OAI.Falconer.exists_policy_scalar_conversion)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_policy_scalar_conversion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {σ ε : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (lam T δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r)
    (hzero : ∀ r ≤ 0, Ψ r = 0) (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ K : ℕ, minJet ≤ K ∧ ∀ L : ℕ, ∀ Z : ℝ, 0 < Z → ∃ N₀ : ℕ,
      ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.Z = Z → N₀ ≤ P.N →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^P.a ∧ dist z.1 z.2*(2:ℝ)^P.a ≤ W) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      20*P.σ*(P.N:ℝ) ≤ (P.t:ℝ)-P.a →
      (P.longest:ℝ) ≤ ((P.t:ℝ)-P.a)/2+P.σ*P.N →
      ∀ w₀ : Sphere (m+3),
      (2:ℝ)^(-(P.a:ℝ))*
        (∫ r in Icc ((2:ℝ)^((P.t:ℝ)-1)) ((2:ℝ)^((P.t:ℝ)+1)),
          ‖charFun (maskedCellDistance w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list
            P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)) r‖^2) ≤
      ((2:ℝ)^P.N)^ε*P.envelope K L Ψ+((2:ℝ)^P.N)^(-T) := by
  sorry

end Falconer

end OAI
end

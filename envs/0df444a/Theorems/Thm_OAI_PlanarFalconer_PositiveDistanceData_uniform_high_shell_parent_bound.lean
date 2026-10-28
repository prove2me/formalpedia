-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_uniform_high_shell_parent_bound
-- name    : OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:52:40.236144+00:00
-- url     : https://prove2.me/theorems/ec59ea20-d961-4296-98fb-a8ee9238f80a
-- title:
--   OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellEquation21.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellEquation21.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.PositiveDistanceData`, with `open Set MeasureTheory Filter`):
--
--   ```lean
--   theorem uniform_high_shell_parent_bound {sig lam eps T : ℝ}
--       (hsig : 0 < sig) (heps : 0 < eps) :
--       ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, ∀ (B : ℕ) (δ : ℝ),
--       RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
--       N₀ ≤ d.N → d.sig = sig → d.lam = lam →
--       0 < d.Q.side → d.StronglySeparated → 0 < d.q →
--       d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
--       d.X.length = d.a → d.Y.length = d.a →
--       ∀ v : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → v ≤ d.t →
--       ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
--       (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
--       ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) →
--       (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
--       ∀ H : ℝ, 0 ≤ H →
--       (∀ j ∈ Finset.range (n+1),
--         ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
--           (d.inversePhasedHF v Ψ b.2 ξ).toReal ≤ H) →
--       (2:ℝ)^(-(d.a:ℝ)) *
--         (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖charFun d.weightedDistance r‖^2) ≤
--           ((2:ℝ)^d.N)^eps*H+((2:ℝ)^d.N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PairMaskIndex`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.inverseLeibnizTerms`, `OAI.PlanarFalconer.pairMaskIndices`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.StronglySeparated`, `OAI.PlanarFalconer.PositiveDistanceData.inverseDescriptorList`, `OAI.PlanarFalconer.PositiveDistanceData.inversePhasedHF` and `OAI.PlanarFalconer.PositiveDistanceData.weightedDistance` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_high_shell` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellEquation21.lean (declaration OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound)

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
namespace PositiveDistanceData

theorem uniform_high_shell_parent_bound {sig lam eps T : ℝ}
    (hsig : 0 < sig) (heps : 0 < eps) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, ∀ (B : ℕ) (δ : ℝ),
    RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    N₀ ≤ d.N → d.sig = sig → d.lam = lam →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    d.X.length = d.a → d.Y.length = d.a →
    ∀ v : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → v ≤ d.t →
    ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
    (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
    ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) →
    (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
    ∀ H : ℝ, 0 ≤ H →
    (∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
        (d.inversePhasedHF v Ψ b.2 ξ).toReal ≤ H) →
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖charFun d.weightedDistance r‖^2) ≤
        ((2:ℝ)^d.N)^eps*H+((2:ℝ)^d.N)^(-T) := by
  sorry

end PositiveDistanceData

end PlanarFalconer

end OAI
end

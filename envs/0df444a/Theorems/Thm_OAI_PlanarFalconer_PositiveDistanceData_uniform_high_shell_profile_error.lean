-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_uniform_high_shell_profile_error
-- name    : OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_profile_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:53:43.869376+00:00
-- url     : https://prove2.me/theorems/e450c472-a3d6-44de-882b-27466df51704
-- title:
--   OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_profile_error: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_profile_error` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellProfileMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellProfileMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.PositiveDistanceData`, with `open Set MeasureTheory`):
--
--   ```lean
--   theorem uniform_high_shell_profile_error {sig lam T : ℝ} (hsig : 0 < sig) :
--       ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, ∀ (B : ℕ) (δ : ℝ),
--       RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
--       N₀ ≤ d.N → d.sig = sig → d.lam = lam →
--       0 < d.Q.side → d.StronglySeparated → 0 < d.q →
--       d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
--       d.X.length = d.a → d.Y.length = d.a →
--       ∀ v r : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → (2:ℝ)^(v-1) ≤ r →
--       ‖charFun d.weightedDistance r-d.normalizedHighShellF n v r‖ ≤ ((2:ℝ)^d.N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.StronglySeparated`, `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF` and `OAI.PlanarFalconer.PositiveDistanceData.weightedDistance` (definitions bundle `OAIQ038F000` of this split).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellProfileMass.lean (declaration OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_profile_error)

import Mathlib
import Lean.Elab.Tactic.Omega
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
namespace PositiveDistanceData

theorem uniform_high_shell_profile_error {sig lam T : ℝ} (hsig : 0 < sig) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, ∀ (B : ℕ) (δ : ℝ),
    RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    N₀ ≤ d.N → d.sig = sig → d.lam = lam →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    d.X.length = d.a → d.Y.length = d.a →
    ∀ v r : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → (2:ℝ)^(v-1) ≤ r →
    ‖charFun d.weightedDistance r-d.normalizedHighShellF n v r‖ ≤ ((2:ℝ)^d.N)^(-T) := by
  sorry

end PositiveDistanceData

end PlanarFalconer

end OAI
end

-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_source_positive_distance_suffix
-- name    : OAI.PlanarFalconer.source_positive_distance_suffix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:55:39.576986+00:00
-- url     : https://prove2.me/theorems/2e7bf958-e7aa-415f-b83a-973fe45814bd
-- title:
--   OAI.PlanarFalconer.source_positive_distance_suffix: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.source_positive_distance_suffix` of [lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/SourceSuffixReduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/SourceSuffixReduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem source_positive_distance_suffix {lam sig kap eps : ℝ}
--       (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (heps : 0 < eps) :
--       ∃ N₀ : ℕ, ∀ d : PositiveDistanceData,
--         d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
--         d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 →
--         d.StronglySeparated → d.X.length = d.a → d.Y.length = d.a →
--         ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
--         d.a+100*d.q < d.t → d.t ≤ d.N → d.i+1 ≤ d.J →
--         let A := fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)
--         let p := policyDepth A d.N d.q d.a d.t
--         d.a+d.t < 2*p →
--         d.coincidence ≤ ENNReal.ofReal (((2:ℝ)^d.N)^
--           (A p-intervalMin A p d.t+4000*(lam+sig)+eps)) *
--             ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.intervalMin`, `OAI.PlanarFalconer.policyDepth`, `OAI.PlanarFalconer.sourcePolicyBlock`, `OAI.PlanarFalconer.sourceSmoothingLevels`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.StronglySeparated` and `OAI.PlanarFalconer.PositiveDistanceData.coincidence` (definitions bundle `OAIQ038F000` of this split).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_recursive_energy_rules` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/SourceSuffixReduction.lean (declaration OAI.PlanarFalconer.source_positive_distance_suffix)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ038F000

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem source_positive_distance_suffix {lam sig kap eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (heps : 0 < eps) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 →
      d.StronglySeparated → d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i+1 ≤ d.J →
      let A := fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)
      let p := policyDepth A d.N d.q d.a d.t
      d.a+d.t < 2*p →
      d.coincidence ≤ ENNReal.ofReal (((2:ℝ)^d.N)^
        (A p-intervalMin A p d.t+4000*(lam+sig)+eps)) *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  sorry

end PlanarFalconer

end OAI
end

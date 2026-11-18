-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_computedCoarseIndexedInitialWithWork_bound
-- name    : OAI.EditApproximation.BinaryFraction.computedCoarseIndexedInitialWithWork_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:22:50.694879+00:00
-- url     : https://prove2.me/theorems/48dd0e56-4689-4be3-8531-142b6b1165ea
-- title:
--   OAI.EditApproximation.BinaryFraction.computedCoarseIndexedInitialWithWork_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.computedCoarseIndexedInitialWithWork_bound` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseIndexedWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseIndexedWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`, with `open Filter`):
--
--   ```lean
--   theorem computedCoarseIndexedInitialWithWork_bound :
--       ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
--         B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
--         coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
--         ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
--         (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
--         (coarseIndexedInitialWithWork (inputHeight N ^ 4) (64 * inputHeight N) N hB hq hL x y draws).2 ≤
--           inputHeight N ^ 40 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
--             x y draws + x.length + 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.initialLambda`, `OAI.EditApproximation.initialThresholdQ`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.integerParameters` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.CoarseThresholdDraws` and `OAI.EditApproximation.computedCoarseDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.CoarseGuessIndex` and `OAI.EditApproximation.coarseEntryWidth` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.BinaryFraction.coarseIndexedInitialWithWork` (the published bundle `Def_EditApproxScheme_12`); `OAI.EditApproximation.coarseInitialArrayWork` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedExecutionIndexedCoarseWork_expected_near_linear` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseIndexedWork.lean (declaration OAI.EditApproximation.BinaryFraction.computedCoarseIndexedInitialWithWork_bound)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_14

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

attribute [local irreducible] coarseIndexedInitialWithWork

theorem computedCoarseIndexedInitialWithWork_bound :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (coarseIndexedInitialWithWork (inputHeight N ^ 4) (64 * inputHeight N) N hB hq hL x y draws).2 ≤
        inputHeight N ^ 40 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
          x y draws + x.length + 1) := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end

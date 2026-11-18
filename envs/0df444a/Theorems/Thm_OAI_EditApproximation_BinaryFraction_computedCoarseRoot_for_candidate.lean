-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_computedCoarseRoot_for_candidate
-- name    : OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:26:26.377203+00:00
-- url     : https://prove2.me/theorems/50e8a886-4bbb-4992-a9c1-67a7b2049350
-- title:
--   OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseCandidateWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseCandidateWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`, with `open Filter`):
--
--   ```lean
--   theorem computedCoarseRoot_for_candidate :
--       ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
--         B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
--         coarseEntryWidth x y ≤ N → ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4)
--         (hL : 0 < 64 * inputHeight N)
--         (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
--         let k := coarseGuess (coarseEntryWidth x y) i
--         let root := coarseRootWithWork k (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL
--           (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
--           (coarseEntryTree B d x y) draws 0 (coarseRootShift k)
--         root.1.width ≤ inputHeight N ^ 3 ∧
--         root.2 ≤ inputHeight N ^ 30 * (2 * coarseActiveArrayWork k
--           (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws k + 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.coarseRootWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.initialLambda`, `OAI.EditApproximation.initialThresholdQ`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.integerParameters` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.CoarseThresholdDraws` and `OAI.EditApproximation.computedCoarseDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.coarsePadTo` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.coarseRootShift` and `OAI.EditApproximation.coarseTargetFrame` (the published bundle `Def_EditApproxScheme_09`); `OAI.EditApproximation.CoarseGuessIndex`, `OAI.EditApproximation.coarseEntryTree`, `OAI.EditApproximation.coarseEntryWidth` and `OAI.EditApproximation.coarseGuess` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.coarseActiveArrayWork` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.computedCoarseInitialWithWork_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseCandidateWork.lean (declaration OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate)

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
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

theorem computedCoarseRoot_for_candidate :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4)
      (hL : 0 < 64 * inputHeight N)
      (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
      let k := coarseGuess (coarseEntryWidth x y) i
      let root := coarseRootWithWork k (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B d x y) draws 0 (coarseRootShift k)
      root.1.width ≤ inputHeight N ^ 3 ∧
      root.2 ≤ inputHeight N ^ 30 * (2 * coarseActiveArrayWork k
        (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws k + 1) := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end

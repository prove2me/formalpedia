-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedQueryTemporaryCells_polynomial
-- name    : OAI.EditApproximation.computedQueryTemporaryCells_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:22.149285+00:00
-- url     : https://prove2.me/theorems/4cd653f5-3202-491c-81aa-b3fc644fbf74
-- title:
--   OAI.EditApproximation.computedQueryTemporaryCells_polynomial: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedQueryTemporaryCells_polynomial` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTemporarySpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTemporarySpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter`):
--
--   ```lean
--   theorem computedQueryTemporaryCells_polynomial :
--       ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
--         ∀ (input : ComputedFamilyInput source target N)
--           (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
--         symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
--         (∀ z ∈ source, z < 2 ^ symbolBits) → (∀ z ∈ target, z < 2 ^ symbolBits) →
--         target.length ≤ 2 ^ positionBits → occurrence = occurrenceBuild symbolBits positionBits target.zipIdx →
--         computedQueryTemporaryCells source target N occurrence symbolBits positionBits input ≤ (N + 2) ^ 20
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedQueryTemporaryCells` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryMemo`, `OAI.EditApproximation.PositionCounts` and `OAI.EditApproximation.inputHeight` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.occurrenceBuild` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.ComputedFamilyInput` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.integerBinarySpace_polynomial` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTemporarySpace.lean (declaration OAI.EditApproximation.computedQueryTemporaryCells_polynomial)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local instance] queryArityNeZero queryRoundsNeZero

theorem computedQueryTemporaryCells_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
        (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      (∀ z ∈ source, z < 2 ^ symbolBits) → (∀ z ∈ target, z < 2 ^ symbolBits) →
      target.length ≤ 2 ^ positionBits → occurrence = occurrenceBuild symbolBits positionBits target.zipIdx →
      computedQueryTemporaryCells source target N occurrence symbolBits positionBits input ≤ (N + 2) ^ 20 := by
  sorry

end EditApproximation

end OAI
end

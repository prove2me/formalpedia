-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedFamilyKernelWork_polynomial
-- name    : OAI.EditApproximation.computedFamilyKernelWork_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:52.922672+00:00
-- url     : https://prove2.me/theorems/5a3be939-22c0-4965-8f7b-b990e1afa69c
-- title:
--   OAI.EditApproximation.computedFamilyKernelWork_polynomial: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedFamilyKernelWork_polynomial` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedBaseStorage.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedBaseStorage.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter`):
--
--   ```lean
--   theorem computedFamilyKernelWork_polynomial (D : ℕ) :
--       ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
--         ∀ (input : ComputedFamilyInput source target N)
--           (cost : ComputedFamilyMemoKey source target N → ℕ),
--         (∀ key, cost key ≤ computedLocalKernelBudget D N) →
--         computedFamilyKernelWork source target N input cost ≤ (N + 2) ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedLocalKernelBudget` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.ComputedFamilyInput` and `OAI.EditApproximation.ComputedFamilyMemoKey` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.computedFamilyKernelWork` (the published bundle `Def_EditApproxScheme_15`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedQueryTemporaryCells_polynomial` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedBaseStorage.lean (declaration OAI.EditApproximation.computedFamilyKernelWork_polynomial)

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
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem computedFamilyKernelWork_polynomial (D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
        (cost : ComputedFamilyMemoKey source target N → ℕ),
      (∀ key, cost key ≤ computedLocalKernelBudget D N) →
      computedFamilyKernelWork source target N input cost ≤ (N + 2) ^ 2 := by
  sorry

end EditApproximation

end OAI
end

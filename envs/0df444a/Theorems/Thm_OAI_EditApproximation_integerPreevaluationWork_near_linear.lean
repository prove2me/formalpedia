-- Prove2me | Theorems.Thm_OAI_EditApproximation_integerPreevaluationWork_near_linear
-- name    : OAI.EditApproximation.integerPreevaluationWork_near_linear
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:21:54.806191+00:00
-- url     : https://prove2.me/theorems/0f9c299c-dd81-42b6-8504-2121a1eb6374
-- title:
--   OAI.EditApproximation.integerPreevaluationWork_near_linear: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.integerPreevaluationWork_near_linear` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPreevaluation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPreevaluation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter`):
--
--   ```lean
--    theorem integerPreevaluationWork_near_linear (C : ℕ) (epsilonTime : ℝ) (htime : 0 < epsilonTime) :
--       ∀ᶠ N in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
--         (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
--         ∀ epsilon : BinaryFraction,
--         (integerPreevaluationWork source target N epsilon : ℝ) ≤
--           (N + 2 : ℝ) ^ (1 + epsilonTime)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.integerPreevaluationWork` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.integerBinarySpace_polynomial` and `OAI.EditApproximation.integerBinaryWork_expected_near_linear` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPreevaluation.lean (declaration OAI.EditApproximation.integerPreevaluationWork_near_linear)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
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
import Definitions.Def_EditApproxScheme_14

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

 theorem integerPreevaluationWork_near_linear (C : ℕ) (epsilonTime : ℝ) (htime : 0 < epsilonTime) :
    ∀ᶠ N in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ epsilon : BinaryFraction,
      (integerPreevaluationWork source target N epsilon : ℝ) ≤
        (N + 2 : ℝ) ^ (1 + epsilonTime) := by
  sorry

end EditApproximation

end OAI
end

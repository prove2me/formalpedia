-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedFamilyResult_requests_near_linear
-- name    : OAI.EditApproximation.computedFamilyResult_requests_near_linear
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:21:52.473461+00:00
-- url     : https://prove2.me/theorems/ceeada44-71ab-4b25-b30b-039d141ff3f4
-- title:
--   OAI.EditApproximation.computedFamilyResult_requests_near_linear: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedFamilyResult_requests_near_linear` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPhysicalWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPhysicalWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter MeasureTheory`):
--
--   ```lean
--    theorem computedFamilyResult_requests_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
--       ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
--         ∀ input : ComputedFamilyInput source target N,
--         ((computedFamilyResult source target N input).requests : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilon)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent`, `OAI.EditApproximation.IntegerParameters` and `OAI.EditApproximation.RecursiveMemoResult` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.intervalTreeDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.ChargedPhysicalRequest` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ComputedFamilyInput` and `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.computedFamilyResult` (the published bundle `Def_EditApproxScheme_16`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedFamilyKernelWork_polynomial`, `OAI.EditApproximation.computedQueryTemporaryCells_polynomial` and `OAI.EditApproximation.integerBinarySpace_polynomial` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPhysicalWork.lean (declaration OAI.EditApproximation.computedFamilyResult_requests_near_linear)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_16

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Filter MeasureTheory

 theorem computedFamilyResult_requests_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      ((computedFamilyResult source target N input).requests : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  sorry

end EditApproximation

end OAI
end

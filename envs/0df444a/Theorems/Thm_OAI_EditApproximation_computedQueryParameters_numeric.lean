-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedQueryParameters_numeric
-- name    : OAI.EditApproximation.computedQueryParameters_numeric
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:12.654149+00:00
-- url     : https://prove2.me/theorems/501fa460-6378-4198-aba9-ce2afab211f3
-- title:
--   OAI.EditApproximation.computedQueryParameters_numeric: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedQueryParameters_numeric` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryConstants.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryConstants.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter`):
--
--   ```lean
--   theorem computedQueryParameters_numeric :
--       ∀ᶠ N : ℕ in atTop, ∀ nx ny, nx + ny ≤ N → ∀ t, t ≤ inputHeight N ^ 2 → ∀ pass,
--         BinaryFraction.PreparedKernelNumericBounds (nx := nx) (ny := ny) (M := (integerParameters N).M)
--           N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
--           (inputHeight N) (inputSmallLog N ^ 80) (heightExponent N / 20) (smallLogExponent N)
--           (inputHeight N ^ 8) (inputHeight N ^ 5)
--           (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
--             (coarseExponent (inputSmallLog N) + 1))) t
--           (computedQueryParameters N 0).tau (computedQueryParameters N pass).factor
--           (computedQueryParameters N 0).eta (computedQueryParameters N 0).kappa
--           (computedQueryParameters N 0).delta (fun _ _ => 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.PreparedKernelNumericBounds` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.coarseExponent`, `OAI.EditApproximation.heightExponent`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent`, `OAI.EditApproximation.IntegerParameters` and `OAI.EditApproximation.RefinementParameterWords` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.computedQueryParameters` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedQueryTable_work_width` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryConstants.lean (declaration OAI.EditApproximation.computedQueryParameters_numeric)

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
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem computedQueryParameters_numeric :
    ∀ᶠ N : ℕ in atTop, ∀ nx ny, nx + ny ≤ N → ∀ t, t ≤ inputHeight N ^ 2 → ∀ pass,
      BinaryFraction.PreparedKernelNumericBounds (nx := nx) (ny := ny) (M := (integerParameters N).M)
        N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8) (inputHeight N ^ 5)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t
        (computedQueryParameters N 0).tau (computedQueryParameters N pass).factor
        (computedQueryParameters N 0).eta (computedQueryParameters N 0).kappa
        (computedQueryParameters N 0).delta (fun _ _ => 0) := by
  sorry

end EditApproximation

end OAI
end

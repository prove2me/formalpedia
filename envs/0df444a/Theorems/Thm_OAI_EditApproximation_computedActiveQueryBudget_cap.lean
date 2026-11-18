-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedActiveQueryBudget_cap
-- name    : OAI.EditApproximation.computedActiveQueryBudget_cap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:32:46.742415+00:00
-- url     : https://prove2.me/theorems/dbc0932a-8f3f-4800-9b2e-433a6334c76b
-- title:
--   OAI.EditApproximation.computedActiveQueryBudget_cap: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedActiveQueryBudget_cap` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTableBudget.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTableBudget.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter`):
--
--   ```lean
--   theorem computedActiveQueryBudget_cap :
--       ∀ᶠ N : ℕ in atTop, ∀ J t : ℕ, J ≤ inputHeight N → t ≤ inputHeight N ^ 2 →
--         computedActiveQueryBudget N J t ≤ computedLocalKernelBudget computedActiveQueryDegree N
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedLocalKernelBudget` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.computedActiveQueryBudget` and `OAI.EditApproximation.computedActiveQueryDegree` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.inputHeight` (the published bundle `Def_EditApproxScheme_01`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedQueryTable_work_width` and `OAI.EditApproximation.integerBinaryWork_expected_near_linear` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTableBudget.lean (declaration OAI.EditApproximation.computedActiveQueryBudget_cap)

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
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryLocalProgramBitDegree queryCallbackShellDegree queryInitialWarmupDegree

theorem computedActiveQueryBudget_cap :
    ∀ᶠ N : ℕ in atTop, ∀ J t : ℕ, J ≤ inputHeight N → t ≤ inputHeight N ^ 2 →
      computedActiveQueryBudget N J t ≤ computedLocalKernelBudget computedActiveQueryDegree N := by
  sorry

end EditApproximation

end OAI
end

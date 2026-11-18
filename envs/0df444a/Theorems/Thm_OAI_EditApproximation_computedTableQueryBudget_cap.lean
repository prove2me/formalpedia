-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedTableQueryBudget_cap
-- name    : OAI.EditApproximation.computedTableQueryBudget_cap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:49.305047+00:00
-- url     : https://prove2.me/theorems/3cdea1e3-3a55-4c75-ab21-b9bea4a026d4
-- title:
--   OAI.EditApproximation.computedTableQueryBudget_cap: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedTableQueryBudget_cap` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTableBudget.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTableBudget.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter`):
--
--   ```lean
--   theorem computedTableQueryBudget_cap :
--       ∀ᶠ N : ℕ in atTop, ∀ Amax J symbolBits positionBits t : ℕ,
--         Amax ≤ computedLocalKernelBudget 1 N → J ≤ inputHeight N →
--         symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 → t ≤ inputHeight N ^ 2 →
--         computedTableQueryBudget N Amax J symbolBits positionBits t ≤
--           computedLocalKernelBudget computedTableQueryDegree N
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedLocalKernelBudget` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.computedTableQueryBudget` and `OAI.EditApproximation.computedTableQueryDegree` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.inputHeight` (the published bundle `Def_EditApproxScheme_01`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedQueryTable_work_width` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTableBudget.lean (declaration OAI.EditApproximation.computedTableQueryBudget_cap)

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

theorem computedTableQueryBudget_cap :
    ∀ᶠ N : ℕ in atTop, ∀ Amax J symbolBits positionBits t : ℕ,
      Amax ≤ computedLocalKernelBudget 1 N → J ≤ inputHeight N →
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 → t ≤ inputHeight N ^ 2 →
      computedTableQueryBudget N Amax J symbolBits positionBits t ≤
        computedLocalKernelBudget computedTableQueryDegree N := by
  sorry

end EditApproximation

end OAI
end

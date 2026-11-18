-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryChargedWarmup_refines
-- name    : OAI.EditApproximation.queryChargedWarmup_refines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:15.032208+00:00
-- url     : https://prove2.me/theorems/ab4b912c-de8a-4586-a640-c242b041ad6b
-- title:
--   OAI.EditApproximation.queryChargedWarmup_refines: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryChargedWarmup_refines` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedWarmup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedWarmup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem queryChargedWarmup_refines (factor : ℕ → ℚ) (hA : A.value = factor parent.val.pass) (hP : 0 < P)
--       (ha : a.value = refinementFactor A.value F)
--       (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
--       (hp : target.length ≤ 2 ^ positionBits)
--       (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx) :
--       BitQuery.Refines (fun word value => word.value = value)
--         (queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits)
--         (chargedWarmupQuery source target N P F factor multiplier parent)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BitQuery.Refines` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BinaryMemo`, `OAI.EditApproximation.PositionCounts` and `OAI.EditApproximation.refinementFactor` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest`, `OAI.EditApproximation.PhysicalTableRequest` and `OAI.EditApproximation.PhysicalTableRequest.Bounded` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.occurrenceBuild` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.chargedWarmupQuery` and `OAI.EditApproximation.ChargedPhysicalRequest.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.queryChargedWarmup` (the published bundle `Def_EditApproxScheme_15`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedQueryMemoNormalized_correct` and `OAI.EditApproximation.computedQueryMemoNormalized_width` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedWarmup.lean (declaration OAI.EditApproximation.queryChargedWarmup_refines)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Warmup
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)

theorem queryChargedWarmup_refines (factor : ℕ → ℚ) (hA : A.value = factor parent.val.pass) (hP : 0 < P)
    (ha : a.value = refinementFactor A.value F)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits)
      (chargedWarmupQuery source target N P F factor multiplier parent) := by
  sorry

end Warmup
end EditApproximation

end OAI
end

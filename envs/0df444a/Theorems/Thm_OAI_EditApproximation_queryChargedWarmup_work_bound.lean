-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryChargedWarmup_work_bound
-- name    : OAI.EditApproximation.queryChargedWarmup_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:24:25.613204+00:00
-- url     : https://prove2.me/theorems/3568d94d-f78b-46ce-93c9-8bbb0c50d554
-- title:
--   OAI.EditApproximation.queryChargedWarmup_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryChargedWarmup_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedWarmupCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedWarmupCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem queryChargedWarmup_work_bound
--       (hB : 10 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
--       (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
--       (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
--       (ht' : Nat.size (target.length + 1) + 2 ≤ B)
--       (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
--       (hM : Nat.size M ≤ B) (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
--       (hA : A.width ≤ B) (ha : a.width ≤ B) (hAone : 1 ≤ A.value) (hAmax : A.value ≤ Amax)
--       (hp : Nat.size parent.val.pass ≤ B) (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
--       (hv : ∀ key, (oracle key).width ≤ B) (hc : ∀ key, readWork key ≤ C) :
--       (queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits).work
--         oracle readWork ≤ queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.queryChargedWarmupBitBudget` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BinaryMemo` and `OAI.EditApproximation.PositionCounts` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest`, `OAI.EditApproximation.PhysicalTableRequest` and `OAI.EditApproximation.PhysicalTableRequest.Bounded` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ChargedPhysicalRequest.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.queryChargedWarmup` (the published bundle `Def_EditApproxScheme_15`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryChargedFamilyTable_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedWarmupCost.lean (declaration OAI.EditApproximation.queryChargedWarmup_work_bound)

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
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Warmup
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F Amax B C : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (oracle : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J target.length passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

theorem queryChargedWarmup_work_bound
    (hB : 10 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hM : Nat.size M ≤ B) (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
    (hA : A.width ≤ B) (ha : a.width ≤ B) (hAone : 1 ≤ A.value) (hAmax : A.value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hv : ∀ key, (oracle key).width ≤ B) (hc : ∀ key, readWork key ≤ C) :
    (queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits).work
      oracle readWork ≤ queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C := by
  sorry

end Warmup
end EditApproximation

end OAI
end

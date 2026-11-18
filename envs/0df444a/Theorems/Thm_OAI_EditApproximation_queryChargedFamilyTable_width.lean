-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryChargedFamilyTable_width
-- name    : OAI.EditApproximation.queryChargedFamilyTable_width
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:39.869115+00:00
-- url     : https://prove2.me/theorems/bbe314b1-80b2-45ab-81e4-ad742b7cb9e4
-- title:
--   OAI.EditApproximation.queryChargedFamilyTable_width: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryChargedFamilyTable_width` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedTableWidth.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedTableWidth.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryChargedFamilyTable_width
--       (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
--       (hFb : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
--       (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
--       (ht' : Nat.size (target.length + 1) + 2 ≤ B)
--       (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
--       (hMb : Nat.size M ≤ B) (ha : (a parent.val.pass).width ≤ B)
--       (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
--       (hactive : ∀ (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J),
--         ((queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
--           tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow).value
--           (fun key => oracle (Sum.map id (fun child =>
--             ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key))).width ≤
--           preparedKernelWordBudget M B) :
--       ((queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
--         delta multiplier occurrence symbolBits positionBits parent).value oracle).width ≤
--           localWarmupWordBudget M B + preparedKernelWordBudget M B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.queryFamilyBoundedActive`, `OAI.EditApproximation.BinaryFraction.localWarmupWordBudget`, `OAI.EditApproximation.BinaryFraction.preparedKernelWordBudget` and `OAI.EditApproximation.ChargedPhysicalRequest.table_rank_lt` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.queryChargedFamilyTable` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BinaryMemo` and `OAI.EditApproximation.PositionCounts` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.TreeLayer` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BitQuery.value` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest`, `OAI.EditApproximation.PhysicalTableRequest`, `OAI.EditApproximation.PhysicalTableRequest.Bounded` and `OAI.EditApproximation.PhysicalTableRequest.combinedRank` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ChargedPhysicalRequest.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.ChargedFamilyQueryKey` (the published bundle `Def_EditApproxScheme_15`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryChargedFamilyTable_semantic_width` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedTableWidth.lean (declaration OAI.EditApproximation.queryChargedFamilyTable_width)

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
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
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
open BinaryFraction

section Table
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF B : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (oracle : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → BinaryFraction)

theorem queryChargedFamilyTable_width
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hMb : Nat.size M ≤ B) (ha : (a parent.val.pass).width ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hactive : ∀ (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J),
      ((queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
        tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow).value
        (fun key => oracle (Sum.map id (fun child =>
          ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key))).width ≤
        preparedKernelWordBudget M B) :
    ((queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).value oracle).width ≤
        localWarmupWordBudget M B + preparedKernelWordBudget M B := by
  sorry

end Table
end EditApproximation

end OAI
end

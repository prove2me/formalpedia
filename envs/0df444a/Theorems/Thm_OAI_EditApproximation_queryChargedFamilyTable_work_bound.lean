-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryChargedFamilyTable_work_bound
-- name    : OAI.EditApproximation.queryChargedFamilyTable_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:24:43.366369+00:00
-- url     : https://prove2.me/theorems/217c2a14-4636-42c5-96bf-3ad96c10e3ff
-- title:
--   OAI.EditApproximation.queryChargedFamilyTable_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryChargedFamilyTable_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedTableCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedTableCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryChargedFamilyTable_work_bound
--       (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
--       (hFb : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
--       (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
--       (ht' : Nat.size (target.length + 1) + 2 ≤ B)
--       (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
--       (hMb : Nat.size M ≤ B) (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
--       (hT : Nat.size T ≤ B)
--       (hA : (A parent.val.pass).width ≤ B) (ha : (a parent.val.pass).width ≤ B)
--       (hAone : 1 ≤ (A parent.val.pass).value) (hAmax : (A parent.val.pass).value ≤ Amax)
--       (hp : Nat.size parent.val.pass ≤ B) (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
--       (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B) (hc : ∀ key, readWork key ≤ C)
--       (hactive : ∀ (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J),
--         (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
--           tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow).work
--           (fun key => oracle (Sum.map id (fun child =>
--             ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key))
--           (fun key => 1 + readWork (Sum.map id (fun child =>
--             ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key)) ≤ active) :
--       (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
--         delta multiplier occurrence symbolBits positionBits parent).work oracle readWork ≤
--           queryChargedTableBitBudget M P F Amax copies J symbolBits positionBits B C active
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.queryFamilyBoundedActive` and `OAI.EditApproximation.ChargedPhysicalRequest.table_rank_lt` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.queryChargedFamilyTable` and `OAI.EditApproximation.queryChargedTableBitBudget` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BinaryMemo` and `OAI.EditApproximation.PositionCounts` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.TreeLayer` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest`, `OAI.EditApproximation.PhysicalTableRequest`, `OAI.EditApproximation.PhysicalTableRequest.Bounded` and `OAI.EditApproximation.PhysicalTableRequest.combinedRank` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ChargedPhysicalRequest.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.ChargedFamilyQueryKey` (the published bundle `Def_EditApproxScheme_15`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryChargedTableCost.lean (declaration OAI.EditApproximation.queryChargedFamilyTable_work_bound)

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
import Definitions.Def_EditApproxScheme_04
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
  (source target : List ℕ) (N P F exponent H Q eM eF Amax B C active : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (oracle : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → BinaryFraction)
  (readWork : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → ℕ)

local notation "tableOracle" => (fun key => oracle (Sum.inr key))
local notation "tableWork" => (fun key => 1 + readWork (Sum.inr key))

theorem queryChargedFamilyTable_work_bound
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hMb : Nat.size M ≤ B) (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
    (hT : Nat.size T ≤ B)
    (hA : (A parent.val.pass).width ≤ B) (ha : (a parent.val.pass).width ≤ B)
    (hAone : 1 ≤ (A parent.val.pass).value) (hAmax : (A parent.val.pass).value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B) (hc : ∀ key, readWork key ≤ C)
    (hactive : ∀ (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J),
      (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
        tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow).work
        (fun key => oracle (Sum.map id (fun child =>
          ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key))
        (fun key => 1 + readWork (Sum.map id (fun child =>
          ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key)) ≤ active) :
    (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).work oracle readWork ≤
        queryChargedTableBitBudget M P F Amax copies J symbolBits positionBits B C active := by
  sorry

end Table
end EditApproximation

end OAI
end

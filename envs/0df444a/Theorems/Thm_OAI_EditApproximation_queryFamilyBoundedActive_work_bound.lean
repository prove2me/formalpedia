-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryFamilyBoundedActive_work_bound
-- name    : OAI.EditApproximation.queryFamilyBoundedActive_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:37:20.957206+00:00
-- url     : https://prove2.me/theorems/89de50e3-1ee5-4e3b-a669-41b14985d5b2
-- title:
--   OAI.EditApproximation.queryFamilyBoundedActive_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryFamilyBoundedActive_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryBoundedActiveCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryBoundedActiveCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryFamilyBoundedActive_work_bound (V C : ℕ)
--       (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
--         N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
--       (htime : Nat.size (parent.val.index - T) ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
--       (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
--       (hc : ∀ key, readWork key ≤ C)
--       (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
--       (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
--       (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value)
--       (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
--         ((queryPhysicalEarlierRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
--           parent.val.node hbelow parent.val.state input).value tableOracle).value ≤
--         ((queryPhysicalWarmupRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
--           (Nat.sub_pos_of_lt hindex) parent.val.node parent.val.state
--           (physicalChild parent.val.node hbelow input.1) (by change parent.val.node.1.val ≤ parent.val.node.1.val + 1; omega)
--           0 (Nat.zero_le T) input.2.2).value tableOracle).value)
--       (hp : Nat.size parent.val.pass ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
--       (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
--       (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
--       (hrank : Nat.size (parent.val.combinedRank T S) ≤ B)
--       (hbound : Nat.size (localOnlineMassBound M P H) ≤ B) :
--       (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
--         tau a eta kappa delta T S passes copies parent hindex hbelow).work oracle readWork ≤
--         queryLocalProgramBitBudget M N P F exponent eM eF B Scale (parent.val.index - T)
--           (queryPhysicalDataBudget T J B V (50 * B + 21 + C + 1)
--             (queryFamilySourceReadBudget J B (50 * B + 21 + C + 1 + 1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.QueryBoundedChild`, `OAI.EditApproximation.queryFamilyBoundedActive`, `OAI.EditApproximation.queryRestrictedPhysicalOracle`, `OAI.EditApproximation.BinaryFraction.PreparedKernelNumericBounds`, `OAI.EditApproximation.BinaryFraction.queryFamilySourceReadBudget`, `OAI.EditApproximation.BinaryFraction.queryLocalProgramBitBudget`, `OAI.EditApproximation.BinaryFraction.queryPhysicalDataBudget` and `OAI.EditApproximation.BinaryFraction.warmupAverageWordBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.queryActiveOracle` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.TreeLayer` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.localOnlineMassBound`, `OAI.EditApproximation.physicalChild` and `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval`, `OAI.EditApproximation.BitQuery.value` and `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalTableRequest`, `OAI.EditApproximation.queryPhysicalEarlierRead`, `OAI.EditApproximation.queryPhysicalWarmupRead`, `OAI.EditApproximation.PhysicalTableRequest.Bounded`, `OAI.EditApproximation.PhysicalTableRequest.combinedRank` and `OAI.EditApproximation.PhysicalTableRequest.refinement` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryBoundedActiveCost.lean (declaration OAI.EditApproximation.queryFamilyBoundedActive_work_bound)

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
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea003

section

attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Bounded
variable {α : Type*} {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF B E Scale : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (oracle : QueryBoundedChild (σ := PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) (passes + 1) copies T S parent → BinaryFraction)
  (readWork : QueryBoundedChild (σ := PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) (passes + 1) copies T S parent → ℕ)

local notation "rawOracle" => queryRestrictedPhysicalOracle (passes + 1) copies T S parent oracle
local notation "rawWork" => queryRestrictedPhysicalReadWork (passes + 1) copies T S parent readWork
local notation "tableOracle" => (fun key => queryActiveOracle T parent.val hindex S rawOracle (Sum.inr key))
open BinaryFraction

theorem queryFamilyBoundedActive_work_bound (V C : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size (parent.val.index - T) ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (hc : ∀ key, readWork key ≤ C)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value)
    (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
      ((queryPhysicalEarlierRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
        parent.val.node hbelow parent.val.state input).value tableOracle).value ≤
      ((queryPhysicalWarmupRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
        (Nat.sub_pos_of_lt hindex) parent.val.node parent.val.state
        (physicalChild parent.val.node hbelow input.1) (by change parent.val.node.1.val ≤ parent.val.node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value tableOracle).value)
    (hp : Nat.size parent.val.pass ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hrank : Nat.size (parent.val.combinedRank T S) ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B) :
    (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent hindex hbelow).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B Scale (parent.val.index - T)
        (queryPhysicalDataBudget T J B V (50 * B + 21 + C + 1)
          (queryFamilySourceReadBudget J B (50 * B + 21 + C + 1 + 1))) := by
  sorry

end Bounded
end EditApproximation

end OAI
end

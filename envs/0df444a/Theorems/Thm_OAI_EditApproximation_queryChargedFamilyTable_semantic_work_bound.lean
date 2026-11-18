-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryChargedFamilyTable_semantic_work_bound
-- name    : OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:34.454825+00:00
-- url     : https://prove2.me/theorems/c51748bd-51e2-45bb-aa17-eb4390d87acf
-- title:
--   OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryTableSemanticCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryTableSemanticCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryChargedFamilyTable_semantic_work_bound
--       (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
--         N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1)
--         tau (a parent.val.pass) eta kappa delta (fun _ _ => 0))
--       (hPd : ∃ j : ℕ, P = 2 ^ j)
--       (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
--       (ht' : Nat.size (target.length + 1) + 2 ≤ B)
--       (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
--       (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
--       (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
--       (hrank : Nat.size (parent.val.combinedRank T S) ≤ B)
--       (hA : (A parent.val.pass).width ≤ B)
--       (hAone : 1 ≤ (A parent.val.pass).value) (hAmax : (A parent.val.pass).value ≤ Amax)
--       (hp : Nat.size parent.val.pass ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
--       (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
--       (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
--       (hbound : Nat.size (localOnlineMassBound M P H) ≤ B)
--       (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
--       (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
--       (hc : ∀ key, readWork key ≤ C) (hdelta : 0 ≤ delta.value)
--       (hread : ∀ child : {r : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S} //
--           r.val.combinedRank T S < parent.val.combinedRank T S},
--         (oracle (Sum.inr ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)).value =
--           requestValue child.val.val) :
--       (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
--         delta multiplier occurrence symbolBits positionBits parent).work oracle readWork ≤
--           queryChargedTableBitBudget M P F Amax copies J symbolBits positionBits B C activeBudget
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.localRequestValue`, `OAI.EditApproximation.BinaryFraction.PreparedKernelNumericBounds`, `OAI.EditApproximation.BinaryFraction.queryFamilySourceReadBudget`, `OAI.EditApproximation.BinaryFraction.queryLocalProgramBitBudget`, `OAI.EditApproximation.BinaryFraction.queryPhysicalDataBudget`, `OAI.EditApproximation.BinaryFraction.warmupAverageWordBudget` and `OAI.EditApproximation.ChargedPhysicalRequest.table_rank_lt` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.queryChargedFamilyTable` and `OAI.EditApproximation.queryChargedTableBitBudget` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BinaryMemo` and `OAI.EditApproximation.PositionCounts` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalInternalNode` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.localOnlineMassBound` and `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` and `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest`, `OAI.EditApproximation.PhysicalTableRequest`, `OAI.EditApproximation.PhysicalTableRequest.Bounded` and `OAI.EditApproximation.PhysicalTableRequest.combinedRank` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ChargedPhysicalRequest.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.CellGroupDraws` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.ChargedFamilyQueryKey` (the published bundle `Def_EditApproxScheme_15`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedQueryTable_work_width` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryTableSemanticCost.lean (declaration OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound)

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
import Definitions.Def_EditApproxScheme_13
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
attribute [local irreducible] queryFamilyBoundedActive queryFamilyActive queryFamilyRefinement
  queryPhysicalRandomDataRequest queryLocalProgram localRequestValue
open BinaryFraction

section Table
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF Amax B E Scale V C : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (oracle : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → BinaryFraction)
  (readWork : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → ℕ)
  (factor : ℕ → ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau.value eta.value kappa.value delta.value group integer initial
local notation "activeBudget" => queryLocalProgramBitBudget M N P F exponent eM eF B Scale (parent.val.index - T)
  (queryPhysicalDataBudget T J B V (50 * B + 21 + (C + 1) + 1)
    (queryFamilySourceReadBudget J B (50 * B + 21 + (C + 1) + 1 + 1)))

theorem queryChargedFamilyTable_semantic_work_bound
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1)
      tau (a parent.val.pass) eta kappa delta (fun _ _ => 0))
    (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
    (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hrank : Nat.size (parent.val.combinedRank T S) ≤ B)
    (hA : (A parent.val.pass).width ≤ B)
    (hAone : 1 ≤ (A parent.val.pass).value) (hAmax : (A parent.val.pass).value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hc : ∀ key, readWork key ≤ C) (hdelta : 0 ≤ delta.value)
    (hread : ∀ child : {r : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S} //
        r.val.combinedRank T S < parent.val.combinedRank T S},
      (oracle (Sum.inr ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)).value =
        requestValue child.val.val) :
    (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).work oracle readWork ≤
        queryChargedTableBitBudget M P F Amax copies J symbolBits positionBits B C activeBudget := by
  sorry

end Table
end EditApproximation

end OAI
end

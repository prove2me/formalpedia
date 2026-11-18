-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryRefinementGather_refines
-- name    : OAI.EditApproximation.queryRefinementGather_refines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:24:32.949433+00:00
-- url     : https://prove2.me/theorems/9a30020d-2d60-4d84-aac6-73c7deeaecca
-- title:
--   OAI.EditApproximation.queryRefinementGather_refines: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryRefinementGather_refines` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryRefinementGather.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryRefinementGather.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem queryRefinementGather_refines
--       (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R)
--       (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
--         (readEarlier key) (expectedEarlier key))
--       (hc : ∀ key, BitQuery.Refines (fun word value => word.value = value)
--         (readCurrent key) (expectedCurrent key))
--       (ho : ∀ keys words, ((online keys words).1.map BinaryBellmanAction.decode) =
--         expectedOnline keys (words.map BinaryFraction.value))
--       (hs : ∀ keys words, ((selected keys words).1.map BinaryBellmanAction.decode) =
--         expectedSelected keys (words.map BinaryFraction.value))
--       (hn : ∀ earlierKeys earlierWords groups actions keys words,
--         BitQuery.Refines relation (next earlierKeys earlierWords groups actions keys words)
--           (expectedNext earlierKeys (earlierWords.map BinaryFraction.value)
--             (groups.map BinaryBellmanAction.decode) (actions.map BinaryBellmanAction.decode)
--             keys (words.map BinaryFraction.value))) :
--       BitQuery.Refines relation
--         (queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF
--           a t initial draw q readEarlier readCurrent online selected next)
--         (let earlierKeys := orderedInputs historyInputCode (historyInputCode_injective M target.length)
--             (queryEarlierInputCover parent N P F exponent t a.value (fun r => (initial r).1.value) q)
--          FiniteQuery.collect expectedEarlier earlierKeys fun earlierWords =>
--            let actions := expectedOnline earlierKeys earlierWords
--            let sharedKeys := orderedInputs childInputCode (childInputCode_injective M target.length)
--              (querySharedInputCover source target parent N F exponent Q a.value
--                (fun r => (initial r).1.value) q (fun b cell scale sample => (draw b cell scale sample).1))
--            FiniteQuery.collect expectedCurrent sharedKeys fun sharedWords =>
--              let groups := expectedSelected sharedKeys sharedWords
--              let keys := orderedInputs childInputCode (childInputCode_injective M target.length)
--                (actionCurrentInputCover groups ∪ actionCurrentInputCover actions)
--              FiniteQuery.collect expectedCurrent keys
--                (expectedNext earlierKeys earlierWords groups actions keys))
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryBellmanAction.decode` and `OAI.EditApproximation.BitQuery.Refines` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.childInputCode_injective` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.historyInputCode_injective` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryBellmanAction`, `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BitQuery`, `OAI.EditApproximation.FiniteQuery` and `OAI.EditApproximation.RationalBellmanAction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.actionCurrentInputCover` and `OAI.EditApproximation.orderedInputs` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.childInputCode` and `OAI.EditApproximation.historyInputCode` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.groupDyadicScales`, `OAI.EditApproximation.groupSampleCount`, `OAI.EditApproximation.instDecidableEqTargetInterval` and `OAI.EditApproximation.queryEarlierInputCover` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.FiniteQuery.collect` (the published bundle `Def_EditApproxScheme_09`); `OAI.EditApproximation.CountedCellGroupDraws`, `OAI.EditApproximation.groupDyadicScaleAt` and `OAI.EditApproximation.querySharedInputCover` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.queryRefinementGather` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryLocalRandomSources_refines` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryRefinementGather.lean (declaration OAI.EditApproximation.queryRefinementGather_refines)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Simulation
variable {ι β α : Type*} {relation : β → ℚ → Prop}
  (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (a : BinaryFraction) (t : ℕ)
  (initial : TargetInterval target.length → BinaryFraction × ℕ)
  (draw : CountedCellGroupDraws M F Q) (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (online : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (selected : List (Fin M × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (expectedOnline : List (Fin M × ℕ × TargetInterval target.length) → List ℚ →
    List (RationalBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M))
  (expectedSelected : List (Fin M × TargetInterval target.length) → List ℚ →
    List (RationalBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M))
  (next : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)
  (expectedNext : List (Fin M × ℕ × TargetInterval target.length) → List ℚ →
    List (RationalBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (RationalBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List ℚ → FiniteQuery ι)

theorem queryRefinementGather_refines
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R)
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hc : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key))
    (ho : ∀ keys words, ((online keys words).1.map BinaryBellmanAction.decode) =
      expectedOnline keys (words.map BinaryFraction.value))
    (hs : ∀ keys words, ((selected keys words).1.map BinaryBellmanAction.decode) =
      expectedSelected keys (words.map BinaryFraction.value))
    (hn : ∀ earlierKeys earlierWords groups actions keys words,
      BitQuery.Refines relation (next earlierKeys earlierWords groups actions keys words)
        (expectedNext earlierKeys (earlierWords.map BinaryFraction.value)
          (groups.map BinaryBellmanAction.decode) (actions.map BinaryBellmanAction.decode)
          keys (words.map BinaryFraction.value))) :
    BitQuery.Refines relation
      (queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF
        a t initial draw q readEarlier readCurrent online selected next)
      (let earlierKeys := orderedInputs historyInputCode (historyInputCode_injective M target.length)
          (queryEarlierInputCover parent N P F exponent t a.value (fun r => (initial r).1.value) q)
       FiniteQuery.collect expectedEarlier earlierKeys fun earlierWords =>
         let actions := expectedOnline earlierKeys earlierWords
         let sharedKeys := orderedInputs childInputCode (childInputCode_injective M target.length)
           (querySharedInputCover source target parent N F exponent Q a.value
             (fun r => (initial r).1.value) q (fun b cell scale sample => (draw b cell scale sample).1))
         FiniteQuery.collect expectedCurrent sharedKeys fun sharedWords =>
           let groups := expectedSelected sharedKeys sharedWords
           let keys := orderedInputs childInputCode (childInputCode_injective M target.length)
             (actionCurrentInputCover groups ∪ actionCurrentInputCover actions)
           FiniteQuery.collect expectedCurrent keys
             (expectedNext earlierKeys earlierWords groups actions keys)) := by
  sorry

end Simulation
end EditApproximation

end OAI
end

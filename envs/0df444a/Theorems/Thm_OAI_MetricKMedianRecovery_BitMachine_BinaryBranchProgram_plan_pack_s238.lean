-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_plan_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:47:02.241279+00:00
-- url     : https://prove2.me/theorems/13f91f82-cc8e-4871-88d7-4164549bf474
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPhysical.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPhysical.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram`, with `open WordOperations WordList BinaryBranchContext`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma plan_pack_s238 (d : ℕ) (r0 y0 : Fin n) (v : ℚ) (xs : List (BlueDP.Atom (Fin m) (Fin n) (Fin n)))
--       (h : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs))
--       (hcap : 2^m*(2*(BinaryFinSet.encode (Finset.univ : Finset (Fin m))).length+2)≤
--         (pairBits (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c,
--           BinaryFinSet.encode (Finset.univ : Finset (Fin m)))).length.succ^d) :
--       plan d data=encode [BinaryFinSet.table (BlueDP.makePlan blue F label score c r0 y0 v xs h).sel,
--         BinaryFinSet.table (BlueDP.makePlan blue F label score c r0 y0 v xs h).dst]
--   ```
--
--   **Definitions.** The statement is written with `OAI.BlueSubsetDP.Plan` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.BlueDP.Atom`, `OAI.MetricKMedianRecovery.BlueDP.Candidate`, `OAI.MetricKMedianRecovery.RationalSampling.State` and `OAI.MetricKMedianRecovery.RationalSampling.assignmentWeight` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.table` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BlueDP.best` and `OAI.MetricKMedianRecovery.BlueDP.block` (definitions bundle `Q238K011` of this split); `OAI.MetricKMedianRecovery.BlueDP.makePlan` and `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan` (definitions bundle `Q238K029` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPhysical.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K029

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field )
variable {n m : ℕ}
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => BinaryBranchContext.pack δ D F S Δ s colors label k c extra
local notation "blue" => Finset.filter (fun i=>colors i=2) (S\RationalSampling.State.deleted s)
local notation "score" => (fun u v=>RationalSampling.assignmentWeight δ D S Δ s u*δ u v)
lemma plan_pack_s238 (d : ℕ) (r0 y0 : Fin n) (v : ℚ) (xs : List (BlueDP.Atom (Fin m) (Fin n) (Fin n)))
    (h : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs))
    (hcap : 2^m*(2*(BinaryFinSet.encode (Finset.univ : Finset (Fin m))).length+2)≤
      (pairBits (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c,
        BinaryFinSet.encode (Finset.univ : Finset (Fin m)))).length.succ^d) :
    plan d data=encode [BinaryFinSet.table (BlueDP.makePlan blue F label score c r0 y0 v xs h).sel,
      BinaryFinSet.table (BlueDP.makePlan blue F label score c r0 y0 v xs h).dst] := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryObservableBranch_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:05:07.63423+00:00
-- url     : https://prove2.me/theorems/a4750b6e-2e28-44a0-aaad-aa365727700d
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch`, with `open WordOperations WordList BinaryBranchContext BinaryBranchProgram`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_pack_s238r (r0 y0 : Fin n)
--       (hcap : 2^m*(2*(BinaryFinSet.encode (Finset.univ : Finset (Fin m))).length+2)≤
--         (pairBits (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c,
--           BinaryFinSet.encode (Finset.univ : Finset (Fin m)))).length.succ^d)
--       (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
--         (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) :
--       run d (pairBits (data,BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length
--         (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
--         BinaryFinSet.encode (output δ D F S Δ s colors label q c r0 y0 bits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rationalScore`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent` and `OAI.MetricKMedianRecovery.Categorical.Explicit.samples` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.raw` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.output` (definitions bundle `Q238L018` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (q c : ℕ) (extra : List Bool) (d : ℕ)
local notation "data" => BinaryBranchContext.pack δ D F S Δ s colors label q c extra
local notation "blue" => Finset.filter (fun i=>colors i=2) (S\RationalSampling.State.deleted s)
local notation "score" => rationalScore δ D S Δ s
lemma run_pack_s238r (r0 y0 : Fin n)
    (hcap : 2^m*(2*(BinaryFinSet.encode (Finset.univ : Finset (Fin m))).length+2)≤
      (pairBits (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c,
        BinaryFinSet.encode (Finset.univ : Finset (Fin m)))).length.succ^d)
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) :
    run d (pairBits (data,BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length
      (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
      BinaryFinSet.encode (output δ D F S Δ s colors label q c r0 y0 bits) := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

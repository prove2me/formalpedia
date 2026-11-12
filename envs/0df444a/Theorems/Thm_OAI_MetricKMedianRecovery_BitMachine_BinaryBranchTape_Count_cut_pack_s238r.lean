-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchTape_Count_cut_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:56:19.388956+00:00
-- url     : https://prove2.me/theorems/c36e9c2b-719c-4865-a70a-ddf049be4246
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/RandomizedZeroBranch.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RandomizedZeroBranch.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count`, with `open WordOperations WordList BinaryArithmetic BinaryBranchContext`, `open BinaryOpeningPayment (field field_computes )`, `open BinaryCategorical`):
--
--   ```lean
--   lemma cut_pack_s238r {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
--       (colors : Fin n→Fin 3) (label : Fin n→Fin b) (q c : ℕ) (extra w : List Bool) :
--       cut (pairBits (pack δ D F S Δ s colors label q c extra,w))=
--         pairBits (pack δ D F S Δ s colors label q c extra,w.take (count n b s.leaves.length))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.count` (definitions bundle `Q238L018` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut` (definitions bundle `Q238L034` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RandomizedZeroBranch.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes )
open BinaryCategorical
attribute [local irreducible] dimensions Resources.tword Resources.lword Resources.bword BinarySeed.product
attribute [local irreducible] leftShape rightShape BinaryBranchRandomize.csize BinaryBranchRandomize.lsize
attribute [local irreducible] run RawTake.run
lemma cut_pack_s238r {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin b) (q c : ℕ) (extra w : List Bool) :
    cut (pairBits (pack δ D F S Δ s colors label q c extra,w))=
      pairBits (pack δ D F S Δ s colors label q c extra,w.take (count n b s.leaves.length)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count

end OAI
end

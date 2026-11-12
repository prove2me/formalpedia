-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_output_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:02:24.25955+00:00
-- url     : https://prove2.me/theorems/cd2ea5db-ca5e-4926-894a-7ed181728d09
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalOutput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalOutput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma output_pack_s238r (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
--       (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
--       (part : Fin q→Fin a) (hp : Function.Surjective part)
--       (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
--       output g (outputPack ctx part seed)=encode ((drawn
--         (Categorical.Selected.greedyRun part (rule part hp) (fun S=>(G S:ℝ)) seed.1).2 seed.2).map elemBits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238L001` of this split); `OAI.MetricKMedianRecovery.Categorical.OracleSeed`, `OAI.MetricKMedianRecovery.Categorical.Table`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawn` and `OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elemBits` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238L006` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.rule` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.outputPack` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalOutput.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
lemma output_pack_s238r (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
    output g (outputPack ctx part seed)=encode ((drawn
      (Categorical.Selected.greedyRun part (rule part hp) (fun S=>(G S:ℝ)) seed.1).2 seed.2).map elemBits) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

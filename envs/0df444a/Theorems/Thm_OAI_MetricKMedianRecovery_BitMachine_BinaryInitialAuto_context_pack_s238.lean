-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialAuto_context_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:39:10.451208+00:00
-- url     : https://prove2.me/theorems/c605909e-d1e0-4024-9786-7287ffa7005c
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialAuto.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialAuto.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto`, with `open WordOperations WordList BinaryArithmetic RationalLeaves`, `open BinaryOpeningPayment (field )`, `open BinaryFiniteContext (labels setBits)`):
--
--   ```lean
--   lemma context_pack_s238 (v M : ℚ) (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (k : ℕ) :
--       context v (pack distance loc F M k)=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238K017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.pack` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context` (definitions bundle `Q238K026` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialAuto.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack)

import Mathlib
import Definitions.Def_Q238K026

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialAuto
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
lemma context_pack_s238 (v M : ℚ) (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (k : ℕ) :
    context v (pack distance loc F M k)=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0 := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end

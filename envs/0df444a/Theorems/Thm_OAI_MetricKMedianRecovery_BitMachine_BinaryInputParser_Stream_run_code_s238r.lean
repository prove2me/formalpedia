-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInputParser_Stream_run_code_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:37:36.996773+00:00
-- url     : https://prove2.me/theorems/dac393a9-c12c-4bc2-8367-07b902f58eba
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/RationalStream.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/RationalStream.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream`, with `open WordOperations`):
--
--   ```lean
--   lemma run_code_s238r (rs : List ℚ) : run (raw rs)=codes rs
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.raw` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.codes` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run` (definitions bundle `Q238L025` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/RationalStream.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code)

import Mathlib
import Definitions.Def_Q238L025

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream
open WordOperations
attribute [local irreducible] rational
lemma run_code_s238r (rs : List ℚ) : run (raw rs)=codes rs := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

end OAI
end

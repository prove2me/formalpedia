-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_algorithm_output_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.algorithm_output_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:19:53.017222+00:00
-- url     : https://prove2.me/theorems/b2a52bf4-0dbe-4618-ae4d-f702a5010cb1
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.algorithm_output_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.algorithm_output` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuterProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuterProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter`, with `open IntegralAssembly FiniteSampling Sampling.Comparison`):
--
--   ```lean
--   lemma algorithm_output_s238 (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput)
--       (seed : (algorithm v C Q d).Seed I) :
--       (algorithm v C Q d).output I seed=output v C Q d I (List.ofFn seed)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BinaryRandomizedAlgorithm.Seed`, `OAI.MetricKMedianRecovery.BinaryRandomizedAlgorithm.bitCount` and `OAI.MetricKMedianRecovery.BinaryRandomizedAlgorithm.output` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.algorithm` and `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.output` (definitions bundle `Q238K053` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.global_application` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuterProbability.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.algorithm_output)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K053

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open IntegralAssembly FiniteSampling Sampling.Comparison
attribute [local irreducible] output run budget
lemma algorithm_output_s238 (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput)
    (seed : (algorithm v C Q d).Seed I) :
    (algorithm v C Q d).output I seed=output v C Q d I (List.ofFn seed) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end

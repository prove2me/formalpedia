-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_capG_integrable_sum_q44
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.capG_integrable_sum_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:08:19.27097+00:00
-- url     : https://prove2.me/theorems/1e6dc8b5-7116-4bf4-b209-a4306a5967c4
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.capG_integrable_sum_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.capG_integrable_sum` of [lean/OAI/Dynamics/StandardMap/StandardMap/CappedTests.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/CappedTests.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open Set Filter MeasureTheory`, `open scoped Topology Classical ENNReal`):
--
--   ```lean
--   lemma capG_integrable_sum_q44 (α : ℝ) : Integrable (fun d : NonAffineArray => capG α d.val) (S.backwardSum L)
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` and `OAI.StandardMapEntropy.CriticalScaleSequence.backwardSum` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.capG` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proofs of `OAI.StandardMapEntropy.CriticalScaleSequence.capG_integral_decomposition_q44` and `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict_q44` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/CappedTests.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.capG_integrable_sum)

import Mathlib
import Definitions.Def_OAIQ44C002

section

attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical ENNReal
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma capG_integrable_sum_q44 (α : ℝ) : Integrable (fun d : NonAffineArray => capG α d.val) (S.backwardSum L) := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_slowPair_aeterminal_q44
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:13:05.456419+00:00
-- url     : https://prove2.me/theorems/681ba4ad-cef3-4607-9b15-d7b74449e768
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal` of [lean/OAI/Dynamics/StandardMap/StandardMap/RealBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/RealBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped ENNReal Topology Classical`):
--
--   ```lean
--   lemma slowPair_aeterminal_q44 : ∀ᵐd ∂K.terminal,SlowPair (realArray d.val) (999/1000)
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus` and `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.SlowPair` and `OAI.StandardMapEntropy.realArray` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.CriticalScaleSequence.shape_aeterminal_q44` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/RealBridge.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal)

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

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (K : S.LimitLaws)
lemma slowPair_aeterminal_q44 : ∀ᵐd ∂K.terminal,SlowPair (realArray d.val) (999/1000) := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

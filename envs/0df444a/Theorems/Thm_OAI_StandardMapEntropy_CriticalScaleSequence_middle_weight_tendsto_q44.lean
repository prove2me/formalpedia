-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_middle_weight_tendsto_q44
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.middle_weight_tendsto_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:09:30.155792+00:00
-- url     : https://prove2.me/theorems/efcaa959-815c-44d7-928f-bc0b0c3d1acc
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.middle_weight_tendsto_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.middle_weight_tendsto` of [lean/OAI/Dynamics/StandardMap/StandardMap/WeightBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/WeightBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter`, `open scoped ENNReal Topology CompactlySupported Classical`):
--
--   ```lean
--   lemma middle_weight_tendsto_q44 {α η:ℝ} (hη:0<η) (f:DistanceArray→ℝ) (hf:Continuous f)
--       (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (g:C_c(DistanceArray,ℝ))
--       (hg:∀d,0≤g d) (hz:∀d∉middleCapOpen η,g d=0) :
--       Tendsto (fun i => ∫d,g d*f d ∂S.multiLaw i) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime` and `OAI.StandardMapEntropy.CriticalScaleSequence.multiLaw` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.capG` and `OAI.StandardMapEntropy.middleCapOpen` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.CriticalScaleSequence.weight_affine_null_q44` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/WeightBridge.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.middle_weight_tendsto)

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

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence)
lemma middle_weight_tendsto_q44 {α η:ℝ} (hη:0<η) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (g:C_c(DistanceArray,ℝ))
    (hg:∀d,0≤g d) (hz:∀d∉middleCapOpen η,g d=0) :
    Tendsto (fun i => ∫d,g d*f d ∂S.multiLaw i) atTop (𝓝 0) := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

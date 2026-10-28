-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_weight_middle_null
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.weight_middle_null
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T00:15:01.187993+00:00
-- url     : https://prove2.me/theorems/06dc6f5e-b259-4e82-9478-cbdf0540408c
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.weight_middle_null: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.weight_middle_null` of [lean/OAI/Dynamics/StandardMap/StandardMap/WeightBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/WeightBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter`, `open scoped ENNReal Topology CompactlySupported Classical`):
--
--   ```lean
--   lemma weight_middle_null (L:S.LimitLaws) {α:ℝ} (f:DistanceArray→ℝ) (hf:Continuous f)
--       (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f)
--       {η:ℝ} (hη:0<η) : Q.law (middleCapOpen η)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CompactWeightLimit`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.capG`, `OAI.StandardMapEntropy.middleCapOpen`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` and `OAI.StandardMapEntropy.CriticalScaleSequence.multiLaw` (definitions bundle `OAIQ2St000` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.CriticalScaleSequence.capG_limit_balance` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/WeightBridge.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.weight_middle_null)

import Mathlib
import Definitions.Def_OAIQ2St000

section

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
lemma weight_middle_null (L:S.LimitLaws) {α:ℝ} (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f)
    {η:ℝ} (hη:0<η) : Q.law (middleCapOpen η)=0 := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

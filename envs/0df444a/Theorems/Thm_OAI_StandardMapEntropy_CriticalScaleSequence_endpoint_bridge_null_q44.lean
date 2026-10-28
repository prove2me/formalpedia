-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_endpoint_bridge_null_q44
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.endpoint_bridge_null_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:10:11.217761+00:00
-- url     : https://prove2.me/theorems/eb3693d9-4746-4502-925f-b81023008208
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.endpoint_bridge_null_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.endpoint_bridge_null` of [lean/OAI/Dynamics/StandardMap/StandardMap/EndpointObservations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/EndpointObservations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped ENNReal Topology CompactlySupported Classical`):
--
--   ```lean
--   lemma endpoint_bridge_null_q44 (S : CriticalScaleSequence) (K : S.LimitLaws) (select : Bool)
--       (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ)) (W H : EndpointObservation)
--       (q : ℕ) (hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000)
--       (hW : W.inWindow u q) (hH : H.inWindow v q) (j : ArrayTestIndex)
--       (htest : (∀d,W.value d=clippedTest j d) ∨ (∀d,H.value d=clippedTest j d))
--       (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
--       K.selected S select {d | d.val∈endpointBridgeEvent u v W H ηw ηh}=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.ArrayTestIndex`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.EndpointObservation`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.clippedTest`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws`, `OAI.StandardMapEntropy.EndpointObservation.inWindow`, `OAI.StandardMapEntropy.EndpointObservation.value` and `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws.selected` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.endpointBridgeEvent` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proofs of `OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aemulti_q44` and `OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal_q44` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/EndpointObservations.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.endpoint_bridge_null)

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
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
lemma endpoint_bridge_null_q44 (S : CriticalScaleSequence) (K : S.LimitLaws) (select : Bool)
    (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ)) (W H : EndpointObservation)
    (q : ℕ) (hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000)
    (hW : W.inWindow u q) (hH : H.inWindow v q) (j : ArrayTestIndex)
    (htest : (∀d,W.value d=clippedTest j d) ∨ (∀d,H.value d=clippedTest j d))
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    K.selected S select {d | d.val∈endpointBridgeEvent u v W H ηw ηh}=0 := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_bridge_null_terminal_q44
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.bridge_null_terminal_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:08:04.019854+00:00
-- url     : https://prove2.me/theorems/365f2362-ab45-4203-bfaa-767d1adbb94a
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.bridge_null_terminal_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.bridge_null_terminal` of [lean/OAI/Dynamics/StandardMap/StandardMap/LimitBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/LimitBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped ENNReal Topology CompactlySupported Classical`):
--
--   ```lean
--   lemma bridge_null_terminal_q44 (S : CriticalScaleSequence) (K : S.LimitLaws) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
--       (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
--       (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
--       (hW0 : ∀d,0≤arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤arrayObservation B.sh B.th Fh d)
--       (j : ArrayTestIndex)
--       (htest : (∀d,arrayObservation B.sw B.tw Fw d=clippedTest j d) ∨
--         (∀d,arrayObservation B.sh B.th Fh d=clippedTest j d))
--       (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
--       K.terminal {d | d.val∈arrayBridgeEvent B Fw Fh ηw ηh}=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.ArrayTestIndex`, `OAI.StandardMapEntropy.BridgeGrid`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.arrayObservation`, `OAI.StandardMapEntropy.clippedTest` and `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.arrayBridgeEvent` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.CriticalScaleSequence.endpoint_bridge_null_q44` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/LimitBridge.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.bridge_null_terminal)

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
lemma bridge_null_terminal_q44 (S : CriticalScaleSequence) (K : S.LimitLaws) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤arrayObservation B.sh B.th Fh d)
    (j : ArrayTestIndex)
    (htest : (∀d,arrayObservation B.sw B.tw Fw d=clippedTest j d) ∨
      (∀d,arrayObservation B.sh B.th Fh d=clippedTest j d))
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    K.terminal {d | d.val∈arrayBridgeEvent B Fw Fh ηw ηh}=0 := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

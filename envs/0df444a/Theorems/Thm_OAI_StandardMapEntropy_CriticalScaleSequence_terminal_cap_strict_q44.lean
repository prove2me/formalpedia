-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_terminal_cap_strict_q44
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:12:56.33915+00:00
-- url     : https://prove2.me/theorems/9b5b1fa6-1357-477b-a0cc-e88358e8bb66
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict` of [lean/OAI/Dynamics/StandardMap/StandardMap/TerminalStrict.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TerminalStrict.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter`, `open scoped Topology ENNReal Classical`):
--
--   ```lean
--   lemma terminal_cap_strict_q44 {α H:ℝ} (hα:0≤α) (hα1:α≤1) (hH:0<H)
--       (hb:(∫d:NonAffineArray,capF α d.val ∂L.terminal)≤H) :
--       (∑'j:ℕ,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))<H
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` and `OAI.StandardMapEntropy.CriticalScaleSequence.backwardLaw` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.capF` and `OAI.StandardMapEntropy.capG` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proofs of `OAI_StandardMapEntropy_eventually_meanDeficit_small_q44` and `OAI.StandardMapEntropy.no_critical_scale_sequence_q44` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TerminalStrict.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict)

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
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma terminal_cap_strict_q44 {α H:ℝ} (hα:0≤α) (hα1:α≤1) (hH:0<H)
    (hb:(∫d:NonAffineArray,capF α d.val ∂L.terminal)≤H) :
    (∑'j:ℕ,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))<H := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

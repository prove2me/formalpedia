-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_terminal_cap_strict_q3
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict_q3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T04:46:21.177477+00:00
-- url     : https://prove2.me/theorems/3eceaf19-0c4d-4485-aecf-ba4f97b4dcdf
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict_q3: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy_complete`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict` of [lean/OAI/Dynamics/StandardMap/StandardMap/TerminalStrict.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TerminalStrict.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter`, `open scoped Topology ENNReal Classical`):
--
--   ```lean
--   lemma terminal_cap_strict_q3 {α H:ℝ} (hα:0≤α) (hα1:α≤1) (hH:0<H)
--       (hb:(∫d:NonAffineArray,capF α d.val ∂L.terminal)≤H) :
--       (∑'j:ℕ,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))<H
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.capF`, `OAI.StandardMapEntropy.capG`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` and `OAI.StandardMapEntropy.CriticalScaleSequence.backwardLaw` (definitions bundle `OAIQ3St000` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.eventually_meanDeficit_small_q3` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TerminalStrict.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict)

import Mathlib
import Definitions.Def_OAIQ3St000

section

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
lemma terminal_cap_strict_q3 {α H:ℝ} (hα:0≤α) (hα1:α≤1) (hH:0<H)
    (hb:(∫d:NonAffineArray,capF α d.val ∂L.terminal)≤H) :
    (∑'j:ℕ,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))<H := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

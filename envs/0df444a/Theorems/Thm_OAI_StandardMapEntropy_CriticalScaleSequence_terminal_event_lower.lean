-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_terminal_event_lower
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T00:14:33.017854+00:00
-- url     : https://prove2.me/theorems/a475f7a1-f5a1-490d-a6b0-5cf76f20ac69
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower` of [lean/OAI/Dynamics/StandardMap/StandardMap/TerminalStrict.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TerminalStrict.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter`, `open scoped Topology ENNReal Classical`):
--
--   ```lean
--   lemma terminal_event_lower {α:ℝ} (hα:0≤α) (hα1:α≤1) (hne:L.terminal≠0) :
--       ∃δ:ℝ,0<δ ∧ ∀ᶠn:ℕ in atTop,δ≤∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.capF`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` and `OAI.StandardMapEntropy.CriticalScaleSequence.backwardLaw` (definitions bundle `OAIQ2St000` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/TerminalStrict.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower)

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
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)

lemma terminal_event_lower {α:ℝ} (hα:0≤α) (hα1:α≤1) (hne:L.terminal≠0) :
    ∃δ:ℝ,0<δ ∧ ∀ᶠn:ℕ in atTop,δ≤∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

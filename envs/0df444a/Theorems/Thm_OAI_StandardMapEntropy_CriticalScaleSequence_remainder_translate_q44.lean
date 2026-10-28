-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_translate_q44
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:12:24.94498+00:00
-- url     : https://prove2.me/theorems/e091df88-fbd8-45b1-aa2b-ae0cbfc9c9b3
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate` of [lean/OAI/Dynamics/StandardMap/StandardMap/RemainderLaws.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/RemainderLaws.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter`, `open scoped ENNReal Topology Classical`):
--
--   ```lean
--   lemma remainder_translate_q44 (r : DyadicTime) : (S.remainderLaw L).map (nonaffineTranslation r)=S.remainderLaw L
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` and `OAI.StandardMapEntropy.CriticalScaleSequence.remainderLaw` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.nonaffineTranslation` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proofs of `OAI_StandardMapEntropy_CriticalScaleSequence_remainder_cap_band_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_left_ray_zero_q44` and `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_right_ray_zero_q44` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/RemainderLaws.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate)

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
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma remainder_translate_q44 (r : DyadicTime) : (S.remainderLaw L).map (nonaffineTranslation r)=S.remainderLaw L := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

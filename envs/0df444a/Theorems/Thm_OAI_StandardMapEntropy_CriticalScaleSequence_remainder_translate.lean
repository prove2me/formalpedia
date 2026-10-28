-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_translate
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T00:14:12.585455+00:00
-- url     : https://prove2.me/theorems/9b8e1cb3-30f6-4256-bf15-42256bbf500e
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate` of [lean/OAI/Dynamics/StandardMap/StandardMap/RemainderLaws.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/RemainderLaws.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter`, `open scoped ENNReal Topology Classical`):
--
--   ```lean
--   lemma remainder_translate (r : DyadicTime) : (S.remainderLaw L).map (nonaffineTranslation r)=S.remainderLaw L
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.nonaffineTranslation`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` and `OAI.StandardMapEntropy.CriticalScaleSequence.remainderLaw` (definitions bundle `OAIQ2St000` of this split).
--
--   **Used by.** The proofs of `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_band` and `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/RemainderLaws.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate)

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
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma remainder_translate (r : DyadicTime) : (S.remainderLaw L).map (nonaffineTranslation r)=S.remainderLaw L := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

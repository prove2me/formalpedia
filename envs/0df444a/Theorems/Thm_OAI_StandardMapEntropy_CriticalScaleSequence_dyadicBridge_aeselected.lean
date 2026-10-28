-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_dyadicBridge_aeselected
-- name    : OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T00:12:18.895929+00:00
-- url     : https://prove2.me/theorems/6bbaaadb-f70a-4929-9396-a78e5a10c0fd
-- title:
--   OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected` of [lean/OAI/Dynamics/StandardMap/StandardMap/BridgeExclusions.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BridgeExclusions.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy.CriticalScaleSequence`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped ENNReal Topology CompactlySupported Classical`):
--
--   ```lean
--   lemma dyadicBridge_aeselected (select : Bool) : ∀ᵐ d ∂K.selected S select,DyadicBridgeExclusions d.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicBridgeExclusions`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.NonAffineArray`, `OAI.StandardMapEntropy.affineLocus`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws` and `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws.selected` (definitions bundle `OAIQ2St000` of this split).
--
--   **Used by.** The proofs of `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_shape` and `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BridgeExclusions.lean (declaration OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected)

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

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (K : S.LimitLaws)
lemma dyadicBridge_aeselected (select : Bool) : ∀ᵐ d ∂K.selected S select,DyadicBridgeExclusions d.val := by
  sorry
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

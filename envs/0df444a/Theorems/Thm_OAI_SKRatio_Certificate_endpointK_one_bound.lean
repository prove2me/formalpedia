-- Prove2me | Theorems.Thm_OAI_SKRatio_Certificate_endpointK_one_bound
-- name    : OAI.SKRatio.Certificate.endpointK_one_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:26:56.321328+00:00
-- url     : https://prove2.me/theorems/7081013a-4b63-4e99-84c3-bd78f3ac5681
-- title:
--   OAI.SKRatio.Certificate.endpointK_one_bound: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Certificate.endpointK_one_bound` of [lean/OAI/Probability/SKRatio/Certificates/CertifiedEndpoints.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/CertifiedEndpoints.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Certificate`, with `open Real MeasureTheory`, `open Scalar`):
--
--   ```lean
--   lemma endpointK_one_bound : endpointK 1 ≤ 902/10000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Scalar.endpointK` (definitions bundle `OAIQ024S010` of this split).
--
--   **Used by.** The proof of `OAI.SKRatio.Certificate.diagonal_envelope` of this split imports it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/CertifiedEndpoints.lean (declaration OAI.SKRatio.Certificate.endpointK_one_bound)

import Mathlib
import Definitions.Def_OAIQ024S010

section

attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma endpointK_one_bound : endpointK 1 ≤ 902/10000 := by
  sorry

end SKRatio.Certificate

end

end OAI
end

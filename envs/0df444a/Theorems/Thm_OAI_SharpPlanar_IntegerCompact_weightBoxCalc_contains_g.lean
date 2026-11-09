-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightBoxCalc_contains_g
-- name    : OAI.SharpPlanar.IntegerCompact.weightBoxCalc_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T00:47:05.48109+00:00
-- url     : https://prove2.me/theorems/a680d5b5-03af-4cc1-b43c-bbf96133b834
-- title:
--   OAI.SharpPlanar.IntegerCompact.weightBoxCalc_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerCompact.weightBoxCalc_contains` of [lean/OAI/Analysis/PlanarPacking/Fejer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerCompact`, with `open IntegerIntervals`):
--
--   ```lean
--   lemma weightBoxCalc_contains_g (v : ℕ) : (weightBoxCalc v).Contains (fejerWeight v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.fejerWeight` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.IntegerCompact.weightBoxCalc` (definitions bundle `OAIQ098G086` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerCompact.weight100_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight101_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight16_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight176_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight177_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight178_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight179_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight180_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight181_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight182_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight183_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight184_contains_g`, `OAI.SharpPlanar.IntegerCompact.weight185_contains_g`, `OAI.SharpPlanar.IntegerCompact.weightRows_contains_g`, `OAI.SharpPlanar.IntegerCompact.weights0_contains_g`, `OAI.SharpPlanar.IntegerCompact.weights10_contains_g`, `OAI.SharpPlanar.IntegerCompact.weights15_contains_g`, `OAI.SharpPlanar.IntegerCompact.weights7_contains_g`, `OAI.SharpPlanar.IntegerCompact.weights8_contains_g` and `OAI.SharpPlanar.IntegerCompact.weights9_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean (declaration OAI.SharpPlanar.IntegerCompact.weightBoxCalc_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G086

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
lemma weightBoxCalc_contains_g (v : ℕ) : (weightBoxCalc v).Contains (fejerWeight v) := by
  sorry

end SharpPlanar.IntegerCompact

end OAI
end

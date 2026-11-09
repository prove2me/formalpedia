-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots25_contains_g
-- name    : OAI.SharpPlanar.IntegerCompact.roots25_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T00:41:24.630304+00:00
-- url     : https://prove2.me/theorems/2a493754-c76d-410c-8d55-794b26a0bbbf
-- title:
--   OAI.SharpPlanar.IntegerCompact.roots25_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerCompact.roots25_contains` of [lean/OAI/Analysis/PlanarPacking/Fejer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerCompact`, with `open IntegerIntervals`):
--
--   ```lean
--   lemma roots25_contains_g (j : Fin 32) : (roots25 j).Contains (rootPhase (800+j.val))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerCompact.roots25` (definitions bundle `OAIQ098G064` of this split); `OAI.SharpPlanar.rootPhase` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerCompact.weightBoxCalc_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean (declaration OAI.SharpPlanar.IntegerCompact.roots25_contains)

import Mathlib
import Definitions.Def_OAIQ098G064
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
lemma roots25_contains_g (j : Fin 32) : (roots25 j).Contains (rootPhase (800+j.val)) := by
  sorry
end SharpPlanar.IntegerCompact

end OAI
end

-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_amp4_12_eq_g
-- name    : OAI.SharpPlanar.CachedData.amp4_12_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T21:07:35.894798+00:00
-- url     : https://prove2.me/theorems/addb18b0-babc-48b7-8f0d-8ed6f2d68f66
-- title:
--   OAI.SharpPlanar.CachedData.amp4_12_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.amp4_12_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma amp4_12_eq_g (i k : Fin 16) : amp4_1Expr 2 i k = amp4_12 i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.amp4_1Expr` (definitions bundle `OAIQ098G020` of this split); `OAI.SharpPlanar.CachedData.amp4_12` (definitions bundle `OAIQ098G021` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.CachedData.amp4_1_eq_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean (declaration OAI.SharpPlanar.CachedData.amp4_12_eq)

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma amp4_12_eq_g (i k : Fin 16) : amp4_1Expr 2 i k = amp4_12 i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end

-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_cm27_1_0_0_s4_eq_g
-- name    : OAI.SharpPlanar.CachedData.cm27_1_0_0.s4_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T08:18:47.730331+00:00
-- url     : https://prove2.me/theorems/ef132dda-6144-4b09-9eea-390541f07fb4
-- title:
--   OAI.SharpPlanar.CachedData.cm27_1_0_0.s4_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.cm27_1_0_0.s4_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/UMoments27.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments27.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.cm27_1_0_0`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma s4_eq_g (i : Fin 16) : chunk 4 i = s4 i
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.cm27_1_0_0.chunk` and `OAI.SharpPlanar.CachedData.cm27_1_0_0.s4` (definitions bundle `OAIQ098G133` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Numerical.U27.entry0_0_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments27.lean (declaration OAI.SharpPlanar.CachedData.cm27_1_0_0.s4_eq)

import Mathlib
import Definitions.Def_OAIQ098G133

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm27_1_0_0
lemma s4_eq_g (i : Fin 16) : chunk 4 i = s4 i := by
  sorry
end cm27_1_0_0
end SharpPlanar.CachedData

end OAI
end

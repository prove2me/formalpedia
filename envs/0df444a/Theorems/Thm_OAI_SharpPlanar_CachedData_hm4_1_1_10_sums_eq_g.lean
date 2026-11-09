-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm4_1_1_10_sums_eq_g
-- name    : OAI.SharpPlanar.CachedData.hm4_1_1_10.sums_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T00:28:04.973463+00:00
-- url     : https://prove2.me/theorems/55247716-b0ed-4fc0-9546-bd3430907fa5
-- title:
--   OAI.SharpPlanar.CachedData.hm4_1_1_10.sums_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm4_1_1_10.sums_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock4_11.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock4_11.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm4_1_1_10`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma sums_eq_g (j : Fin 6) (i : Fin 16) : chunk j i = sums j i
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.hm4_1_1_10.sums` (definitions bundle `OAIQ098G1295` of this split); `OAI.SharpPlanar.CachedData.hm4_1_1_10.chunk` (definitions bundle `OAIQ098G1297` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Bernstein4.N0_right.t8_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock4_11.lean (declaration OAI.SharpPlanar.CachedData.hm4_1_1_10.sums_eq)

import Mathlib
import Definitions.Def_OAIQ098G1295
import Definitions.Def_OAIQ098G1297

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm4_1_1_10
lemma sums_eq_g (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  sorry
end hm4_1_1_10
end SharpPlanar.CachedData

end OAI
end

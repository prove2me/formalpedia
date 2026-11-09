-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_column91_0_eq_g
-- name    : OAI.SharpPlanar.CachedData.column91_0_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T22:16:01.19367+00:00
-- url     : https://prove2.me/theorems/3b33e900-f4a6-40af-9cec-277682d435eb
-- title:
--   OAI.SharpPlanar.CachedData.column91_0_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.column91_0_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/Columns100.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns100.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma column91_0_eq_g (j : Fin 6) (i k : Fin 16) : column91_0Expr j i k = column91_0 j i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.column91_0` (definitions bundle `OAIQ098G226` of this split); `OAI.SharpPlanar.CachedData.column91_0Expr` (definitions bundle `OAIQ098G296` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.CachedData.column91_0_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns100.lean (declaration OAI.SharpPlanar.CachedData.column91_0_eq)

import Mathlib
import Definitions.Def_OAIQ098G226
import Definitions.Def_OAIQ098G296

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column91_0_eq_g (j : Fin 6) (i k : Fin 16) : column91_0Expr j i k = column91_0 j i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end

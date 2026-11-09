-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_tm0_21_0_sums_eq_g
-- name    : OAI.SharpPlanar.CachedData.tm0_21_0.sums_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T02:02:47.060962+00:00
-- url     : https://prove2.me/theorems/2e14a3c6-098d-464c-9fad-173449a9ee77
-- title:
--   OAI.SharpPlanar.CachedData.tm0_21_0.sums_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.tm0_21_0.sums_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments21.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments21.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.tm0_21_0`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma sums_eq_g (j : Fin 6) (i : Fin 16) : chunk j i = sums j i
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.tm0_21_0.chunk` (definitions bundle `OAIQ098G1505` of this split); `OAI.SharpPlanar.CachedData.tm0_21_0.sums` (definitions bundle `OAIQ098G1506` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Residual21.bound1_1_g` and `OAI.SharpPlanar.residual_finite_exterior_1_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments21.lean (declaration OAI.SharpPlanar.CachedData.tm0_21_0.sums_eq)

import Mathlib
import Definitions.Def_OAIQ098G1505
import Definitions.Def_OAIQ098G1506

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_21_0
lemma sums_eq_g (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  sorry
end tm0_21_0

end SharpPlanar.CachedData

end OAI
end

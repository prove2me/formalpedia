-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_10_eq_g
-- name    : OAI.SharpPlanar.CachedData.mpower0_10_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T22:05:41.705968+00:00
-- url     : https://prove2.me/theorems/9246a742-605c-4fdd-8e59-4e324e7c7707
-- title:
--   OAI.SharpPlanar.CachedData.mpower0_10_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.mpower0_10_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma mpower0_10_eq_g (j : Fin 6) (i k : Fin 16) : mpower0_10Expr j i k = mpower0_10 j i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.mpower0_10Expr` (definitions bundle `OAIQ098G1459` of this split); `OAI.SharpPlanar.CachedData.mpower0_10` (definitions bundle `OAIQ098G419` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein16.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein1.N0_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hm12_1_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm13_0_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm13_1_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm19_0_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm19_1_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_10.contains_g`, `OAI.SharpPlanar.CachedData.hm21_0_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm21_1_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_0_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_1_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm3_0_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm3_1_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_0_0_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm4_1_0_10.realContains_g` and `OAI.SharpPlanar.CachedData.hm7_0_0_10.realContains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean (declaration OAI.SharpPlanar.CachedData.mpower0_10_eq)

import Mathlib
import Definitions.Def_OAIQ098G419
import Definitions.Def_OAIQ098G1459

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma mpower0_10_eq_g (j : Fin 6) (i k : Fin 16) : mpower0_10Expr j i k = mpower0_10 j i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end

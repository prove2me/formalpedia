-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_8_eq_g
-- name    : OAI.SharpPlanar.CachedData.mpower1_8_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T22:10:44.790196+00:00
-- url     : https://prove2.me/theorems/93af0d84-244f-476e-a2dc-57f41cdbb9c5
-- title:
--   OAI.SharpPlanar.CachedData.mpower1_8_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.mpower1_8_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma mpower1_8_eq_g (j : Fin 6) (i k : Fin 16) : mpower1_8Expr j i k = mpower1_8 j i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.mpower1_8Expr` (definitions bundle `OAIQ098G1491` of this split); `OAI.SharpPlanar.CachedData.mpower1_8` (definitions bundle `OAIQ098G475` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein12.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein13.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein13.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein13.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein13.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein19.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein19.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein19.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein19.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein27.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein27.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein27.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein27.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_right.t6_contains_g`, `OAI.SharpPlanar.CachedData.hm1_0_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm21_1_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_0_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_1_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_0_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_1_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm28_0_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm28_1_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm7_0_1_8.realContains_g` and `OAI.SharpPlanar.CachedData.mpower1_9_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean (declaration OAI.SharpPlanar.CachedData.mpower1_8_eq)

import Mathlib
import Definitions.Def_OAIQ098G475
import Definitions.Def_OAIQ098G1491

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma mpower1_8_eq_g (j : Fin 6) (i k : Fin 16) : mpower1_8Expr j i k = mpower1_8 j i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end

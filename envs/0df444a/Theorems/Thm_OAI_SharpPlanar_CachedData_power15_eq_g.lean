-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power15_eq_g
-- name    : OAI.SharpPlanar.CachedData.power15_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T00:38:56.603194+00:00
-- url     : https://prove2.me/theorems/76d1d6fa-87b9-497c-b1bf-1070c87f8377
-- title:
--   OAI.SharpPlanar.CachedData.power15_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power15_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power15_eq_g (j : Fin 6) (i k : Fin 16) : power15Expr j i k = power15 j i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.power15` (definitions bundle `OAIQ098G241` of this split); `OAI.SharpPlanar.CachedData.power15Expr` (definitions bundle `OAIQ098G311` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein15.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein15.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein15.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein15.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein15.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein15.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hm15_1_0_6.contains_g`, `OAI.SharpPlanar.CachedData.hm16_0_0_13.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_0_3.contains_g`, `OAI.SharpPlanar.CachedData.hm16_0_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_0_5.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_0_8.contains_g`, `OAI.SharpPlanar.CachedData.hm16_1_0_13.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_0_3.contains_g`, `OAI.SharpPlanar.CachedData.hm16_1_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_0_5.realContains_g` and `OAI.SharpPlanar.CachedData.hm16_1_0_8.contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean (declaration OAI.SharpPlanar.CachedData.power15_eq)

import Mathlib
import Definitions.Def_OAIQ098G241
import Definitions.Def_OAIQ098G311

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power15_eq_g (j : Fin 6) (i k : Fin 16) : power15Expr j i k = power15 j i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end

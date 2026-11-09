-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_kernel1_0_eq_g
-- name    : OAI.SharpPlanar.CachedData.kernel1_0_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T22:02:19.600404+00:00
-- url     : https://prove2.me/theorems/625bf4bd-90e4-4060-b0dc-7e2c76cd6ebb
-- title:
--   OAI.SharpPlanar.CachedData.kernel1_0_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.kernel1_0_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma kernel1_0_eq_g (j : Fin 6) (i k : Fin 16) : kernel1_0Expr j i k = kernel1_0 j i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.kernel1_0` (definitions bundle `OAIQ098G023` of this split); `OAI.SharpPlanar.CachedData.kernel1_0Expr` (definitions bundle `OAIQ098G061` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein1.N0_right.t27_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t13_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t18_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t26_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t28_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t13_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t18_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t26_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t28_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_21_contains_g`, `OAI.SharpPlanar.CachedData.hm1_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_10.contains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_11.contains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_13.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_18.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_22.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_23.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_8.realContains_g`, `OAI.SharpPlanar.Numerical.dentry0_1_contains_g` and `OAI.SharpPlanar.Numerical.dentry3_4_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues10.lean (declaration OAI.SharpPlanar.CachedData.kernel1_0_eq)

import Mathlib
import Definitions.Def_OAIQ098G023
import Definitions.Def_OAIQ098G061

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma kernel1_0_eq_g (j : Fin 6) (i k : Fin 16) : kernel1_0Expr j i k = kernel1_0 j i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end

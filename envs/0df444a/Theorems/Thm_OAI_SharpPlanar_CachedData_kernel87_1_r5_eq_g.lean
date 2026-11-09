-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_kernel87_1_r5_eq_g
-- name    : OAI.SharpPlanar.CachedData.kernel87_1_r5_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T03:06:21.167243+00:00
-- url     : https://prove2.me/theorems/fa8f42f7-56a9-43cb-8707-ba8f9debde50
-- title:
--   OAI.SharpPlanar.CachedData.kernel87_1_r5_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.kernel87_1_r5_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues90.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues90.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma kernel87_1_r5_eq_g (i k : Fin 16) : kernel87_1Expr 5 i k = kernel87_1_r5 i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.kernel87_1_r5` (definitions bundle `OAIQ098G1449` of this split); `OAI.SharpPlanar.CachedData.kernel87_1Expr` (definitions bundle `OAIQ098G1451` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.CachedData.kernel87_1_eq_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues90.lean (declaration OAI.SharpPlanar.CachedData.kernel87_1_r5_eq)

import Mathlib
import Definitions.Def_OAIQ098G1451

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma kernel87_1_r5_eq_g (i k : Fin 16) : kernel87_1Expr 5 i k = kernel87_1_r5 i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end

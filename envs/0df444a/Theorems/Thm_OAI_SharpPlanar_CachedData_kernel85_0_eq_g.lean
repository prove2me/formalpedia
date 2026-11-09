-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_kernel85_0_eq_g
-- name    : OAI.SharpPlanar.CachedData.kernel85_0_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T01:59:53.889311+00:00
-- url     : https://prove2.me/theorems/3d365645-b4d6-4c4a-8135-7a8ff14d156b
-- title:
--   OAI.SharpPlanar.CachedData.kernel85_0_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.kernel85_0_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues90.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues90.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma kernel85_0_eq_g (j : Fin 6) (i k : Fin 16) : kernel85_0Expr j i k = kernel85_0 j i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.kernel85_0` (definitions bundle `OAIQ098G1446` of this split); `OAI.SharpPlanar.CachedData.kernel85_0Expr` (definitions bundle `OAIQ098G1448` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Residual85.bound0_0_g`, `OAI.SharpPlanar.Residual85.bound0_1_g`, `OAI.SharpPlanar.Residual85.bound1_0_g` and `OAI.SharpPlanar.Residual85.bound1_1_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues90.lean (declaration OAI.SharpPlanar.CachedData.kernel85_0_eq)

import Mathlib
import Definitions.Def_OAIQ098G1448

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma kernel85_0_eq_g (j : Fin 6) (i k : Fin 16) : kernel85_0Expr j i k = kernel85_0 j i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end

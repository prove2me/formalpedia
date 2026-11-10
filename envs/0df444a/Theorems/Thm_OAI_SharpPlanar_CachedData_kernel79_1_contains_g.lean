-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_kernel79_1_contains_g
-- name    : OAI.SharpPlanar.CachedData.kernel79_1_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T01:55:50.026938+00:00
-- url     : https://prove2.me/theorems/7d1a9de3-9c9f-4444-a857-01bd9fd2287d
-- title:
--   OAI.SharpPlanar.CachedData.kernel79_1_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.kernel79_1_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues80.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues80.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma kernel79_1_contains_g (j : Fin 6) (i k : Fin 16) :
--       (kernel79_1 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
--         Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(79:ℕ))*
--         (if true then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.lambda` and `OAI.SharpPlanar.z` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.kernel79_1` (definitions bundle `OAIQ098G1443` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Residual79.bound0_1_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues80.lean (declaration OAI.SharpPlanar.CachedData.kernel79_1_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1443

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma kernel79_1_contains_g (j : Fin 6) (i k : Fin 16) :
    (kernel79_1 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(79:ℕ))*
      (if true then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  sorry
end SharpPlanar.CachedData

end OAI
end

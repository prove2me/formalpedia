-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_kernel79_0_contains_e
-- name    : OAI.SharpPlanar.CachedData.kernel79_0_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T23:39:35.020101+00:00
-- url     : https://prove2.me/theorems/d18bddf0-824d-4bd7-be12-d5ad5c935a16
-- title:
--   OAI.SharpPlanar.CachedData.kernel79_0_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.kernel79_0_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues80.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues80.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma kernel79_0_contains_e (j : Fin 6) (i k : Fin 16) :
--       (kernel79_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
--         Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(79:ℕ))*
--         (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.lambda` and `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.kernel79_0` (definitions bundle `OAIQ098E225` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Residual79.bound0_1_e`, `OAI.SharpPlanar.Residual79.bound1_1_e`, `OAI.SharpPlanar.residual_finite_exterior_0_e` and `OAI.SharpPlanar.residual_finite_exterior_1_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues80.lean (declaration OAI.SharpPlanar.CachedData.kernel79_0_contains)

import Mathlib
import Definitions.Def_OAIQ098E225

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma kernel79_0_contains_e (j : Fin 6) (i k : Fin 16) :
    (kernel79_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(79:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  sorry
end SharpPlanar.CachedData

end OAI
end

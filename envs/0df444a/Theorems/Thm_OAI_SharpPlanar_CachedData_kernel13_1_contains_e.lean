-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_kernel13_1_contains_e
-- name    : OAI.SharpPlanar.CachedData.kernel13_1_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T23:34:13.770248+00:00
-- url     : https://prove2.me/theorems/9c57d7d9-b5ee-4c42-83f2-a93f39769734
-- title:
--   OAI.SharpPlanar.CachedData.kernel13_1_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.kernel13_1_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma kernel13_1_contains_e (j : Fin 6) (i k : Fin 16) :
--       (kernel13_1 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
--         Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(13:ℕ))*
--         (if true then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.lambda` and `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.kernel13_1` (definitions bundle `OAIQ098E041` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.Lmat_column_e`, `OAI.SharpPlanar.Numerical.lentry3_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry3_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry9_5_contains_e`, `OAI.SharpPlanar.Residual13.bound0_1_e` and `OAI.SharpPlanar.Residual13.bound1_1_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues20.lean (declaration OAI.SharpPlanar.CachedData.kernel13_1_contains)

import Mathlib
import Definitions.Def_OAIQ098E041

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma kernel13_1_contains_e (j : Fin 6) (i k : Fin 16) :
    (kernel13_1 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(13:ℕ))*
      (if true then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  sorry
end SharpPlanar.CachedData

end OAI
end

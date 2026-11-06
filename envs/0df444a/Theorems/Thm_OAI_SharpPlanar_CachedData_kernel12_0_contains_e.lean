-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_kernel12_0_contains_e
-- name    : OAI.SharpPlanar.CachedData.kernel12_0_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T23:31:23.971504+00:00
-- url     : https://prove2.me/theorems/9cc4e753-e0b4-4bfe-aae0-9b8e56696f18
-- title:
--   OAI.SharpPlanar.CachedData.kernel12_0_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.kernel12_0_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma kernel12_0_contains_e (j : Fin 6) (i k : Fin 16) :
--       (kernel12_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
--         Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(12:ℕ))*
--         (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.lambda` and `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.kernel12_0` (definitions bundle `OAIQ098E041` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein12.N0_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t9_contains_e`, `OAI.SharpPlanar.CachedData.hk12_1_12_contains_e`, `OAI.SharpPlanar.CachedData.hk12_1_2_contains_e`, `OAI.SharpPlanar.CachedData.hm12_0_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_1_1_4.realContains_e`, `OAI.SharpPlanar.Numerical.lentry2_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_5_contains_e`, `OAI.SharpPlanar.Residual12.bound0_1_e`, `OAI.SharpPlanar.Residual12.bound1_1_e`, `OAI.SharpPlanar.residual_finite_exterior_0_e` and `OAI.SharpPlanar.residual_finite_exterior_1_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues20.lean (declaration OAI.SharpPlanar.CachedData.kernel12_0_contains)

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
lemma kernel12_0_contains_e (j : Fin 6) (i k : Fin 16) :
    (kernel12_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(12:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  sorry
end SharpPlanar.CachedData

end OAI
end

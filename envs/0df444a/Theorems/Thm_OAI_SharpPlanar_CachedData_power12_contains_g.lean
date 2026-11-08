-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power12_contains_g
-- name    : OAI.SharpPlanar.CachedData.power12_contains_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T23:39:56.120794+00:00
-- url     : https://prove2.me/theorems/a8e02515-ed51-4bc0-9b4f-f6242f8de188
-- title:
--   OAI.SharpPlanar.CachedData.power12_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power12_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power12_contains_g (j : Fin 6) (i k : Fin 16) :
--       (power12 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(12:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.power12` (definitions bundle `OAIQ098G237` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein12.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein12.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.column12_0_contains_g`, `OAI.SharpPlanar.CachedData.column12_1_contains_g`, `OAI.SharpPlanar.CachedData.hk12_0_2_contains_g`, `OAI.SharpPlanar.CachedData.hk12_0_8_contains_g`, `OAI.SharpPlanar.CachedData.hm12_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm12_0_0_7.realContains_g`, `OAI.SharpPlanar.CachedData.hm12_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm12_1_0_7.realContains_g` and `OAI.SharpPlanar.CachedData.power13_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean (declaration OAI.SharpPlanar.CachedData.power12_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G237

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power12_contains_g (j : Fin 6) (i k : Fin 16) :
    (power12 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(12:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end

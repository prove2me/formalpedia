-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_trans36_contains_g
-- name    : OAI.SharpPlanar.CachedData.trans36_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T21:37:31.37065+00:00
-- url     : https://prove2.me/theorems/9b85e34f-89b6-486e-998e-60e468a30501
-- title:
--   OAI.SharpPlanar.CachedData.trans36_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.trans36_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers40.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers40.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma trans36_contains_g (j : Fin 6) (i k : Fin 16) :
--       (trans36 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(36:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.trans36` (definitions bundle `OAIQ098G1415` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein36.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_right.t3_contains_g`, `OAI.SharpPlanar.CachedData.hk37_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hm36_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm36_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm37_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm37_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.kernel39_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel40_0_contains_g`, `OAI.SharpPlanar.CachedData.trans43_contains_g`, `OAI.SharpPlanar.Residual36.bound0_0_g`, `OAI.SharpPlanar.Residual36.bound0_1_g`, `OAI.SharpPlanar.Residual36.bound1_0_g`, `OAI.SharpPlanar.Residual36.bound1_1_g`, `OAI.SharpPlanar.Residual37.bound0_0_g`, `OAI.SharpPlanar.Residual37.bound0_1_g`, `OAI.SharpPlanar.Residual37.bound1_0_g`, `OAI.SharpPlanar.Residual37.bound1_1_g`, `OAI.SharpPlanar.Residual39.bound0_1_g`, `OAI.SharpPlanar.Residual39.bound1_1_g`, `OAI.SharpPlanar.Residual40.bound0_1_g` and `OAI.SharpPlanar.Residual40.bound1_1_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers40.lean (declaration OAI.SharpPlanar.CachedData.trans36_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1415

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma trans36_contains_g (j : Fin 6) (i k : Fin 16) :
    (trans36 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(36:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end

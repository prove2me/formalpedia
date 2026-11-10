-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power3_contains_g
-- name    : OAI.SharpPlanar.CachedData.power3_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T21:24:55.264968+00:00
-- url     : https://prove2.me/theorems/12c9ead1-82da-4825-aa19-9cee2721881e
-- title:
--   OAI.SharpPlanar.CachedData.power3_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power3_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power3_contains_g (j : Fin 6) (i k : Fin 16) :
--       (power3 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(3:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.CachedData.power3` (definitions bundle `OAIQ098G053` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein3.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.cm3_16_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_3_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_4_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_4_1_1.contains_g`, `OAI.SharpPlanar.CachedData.hm3_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm3_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.power4_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm3_contains_g`, `OAI.SharpPlanar.Numerical.dentry0_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry0_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry3_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry3_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry9_1_contains_g` and `OAI.SharpPlanar.Numerical.lentry9_4_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean (declaration OAI.SharpPlanar.CachedData.power3_contains)

import Mathlib
import Definitions.Def_OAIQ098G053
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power3_contains_g (j : Fin 6) (i k : Fin 16) :
    (power3 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(3:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end

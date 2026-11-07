-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_trans2_contains_e
-- name    : OAI.SharpPlanar.CachedData.trans2_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T10:38:21.211352+00:00
-- url     : https://prove2.me/theorems/3bf92de2-ef46-4fff-99b9-6c136a690640
-- title:
--   OAI.SharpPlanar.CachedData.trans2_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.trans2_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma trans2_contains_e (j : Fin 6) (i k : Fin 16) :
--       (trans2 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(2:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.CachedData.trans2` (definitions bundle `OAIQ098E029` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.kernel3_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel3_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel4_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel4_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel7_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel7_1_contains_e` and `OAI.SharpPlanar.CachedData.trans8_contains_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean (declaration OAI.SharpPlanar.CachedData.trans2_contains)

import Mathlib
import Definitions.Def_OAIQ098E031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma trans2_contains_e (j : Fin 6) (i k : Fin 16) :
    (trans2 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(2:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end

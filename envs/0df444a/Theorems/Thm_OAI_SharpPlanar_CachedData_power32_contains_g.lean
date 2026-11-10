-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power32_contains_g
-- name    : OAI.SharpPlanar.CachedData.power32_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T22:14:04.308592+00:00
-- url     : https://prove2.me/theorems/dc1d4014-090b-4dfe-987a-5e953b4a97cb
-- title:
--   OAI.SharpPlanar.CachedData.power32_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power32_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power32_contains_g (j : Fin 6) (i k : Fin 16) :
--       (power32 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(32:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.power32` (definitions bundle `OAIQ098G319` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein33.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t5_contains_g`, `OAI.SharpPlanar.CachedData.hk33_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hm33_0_0_6.contains_g` and `OAI.SharpPlanar.CachedData.hm33_1_0_6.contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean (declaration OAI.SharpPlanar.CachedData.power32_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G319

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power32_contains_g (j : Fin 6) (i k : Fin 16) :
    (power32 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(32:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end

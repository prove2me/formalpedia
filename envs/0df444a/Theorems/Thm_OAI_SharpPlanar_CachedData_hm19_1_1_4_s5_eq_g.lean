-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm19_1_1_4_s5_eq_g
-- name    : OAI.SharpPlanar.CachedData.hm19_1_1_4.s5_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T22:26:26.127577+00:00
-- url     : https://prove2.me/theorems/27cf8d55-2b0a-4292-8575-b68ca9fccade
-- title:
--   OAI.SharpPlanar.CachedData.hm19_1_1_4.s5_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm19_1_1_4.s5_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock19_10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock19_10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm19_1_1_4`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma s5_eq_g (i : Fin 16) : chunk 5 i = s5 i
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.hm19_1_1_4.s5` (definitions bundle `OAIQ098G924` of this split); `OAI.SharpPlanar.CachedData.hm19_1_1_4.chunk` (definitions bundle `OAIQ098G928` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein19.N0_left.t2_contains_g` and `OAI.SharpPlanar.Bernstein19.N0_right.t2_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock19_10.lean (declaration OAI.SharpPlanar.CachedData.hm19_1_1_4.s5_eq)

import Mathlib
import Definitions.Def_OAIQ098G924
import Definitions.Def_OAIQ098G928

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm19_1_1_4
lemma s5_eq_g (i : Fin 16) : chunk 5 i = s5 i := by
  sorry
end hm19_1_1_4
end SharpPlanar.CachedData

end OAI
end

-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_U40_entry2_1_contains_g
-- name    : OAI.SharpPlanar.Numerical.U40.entry2_1_contains_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-09T19:44:33.395479+00:00
-- url     : https://prove2.me/theorems/80f74fc7-78ec-4b19-a5c7-a69bc7c2beb3
-- title:
--   OAI.SharpPlanar.Numerical.U40.entry2_1_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.U40.entry2_1_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/WUCert40.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert40.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical.U40`, with `open IntegerIntervals IntegerBasis IntegerGrid CachedData`):
--
--   ```lean
--   lemma entry2_1_contains_g : entry2_1.Contains (umat 2 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.Numerical.U40.entry2_1` and `OAI.SharpPlanar.Numerical.U40.umat` (definitions bundle `OAIQ098G362` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.U40.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U40.wuplus_column_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert40.lean (declaration OAI.SharpPlanar.Numerical.U40.entry2_1_contains)

import Mathlib
import Definitions.Def_OAIQ098G362

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical.U40
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma entry2_1_contains_g : entry2_1.Contains (umat 2 1) := by
  sorry
end SharpPlanar.Numerical.U40

end OAI
end

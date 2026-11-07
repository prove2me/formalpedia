-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_U91_entry3_1_contains_e
-- name    : OAI.SharpPlanar.Numerical.U91.entry3_1_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T19:06:03.108079+00:00
-- url     : https://prove2.me/theorems/6245e035-1c30-4efb-8cc8-8b0f546c89d0
-- title:
--   OAI.SharpPlanar.Numerical.U91.entry3_1_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.U91.entry3_1_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/WUCert91.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert91.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical.U91`, with `open IntegerIntervals IntegerBasis IntegerGrid CachedData`):
--
--   ```lean
--   lemma entry3_1_contains_e : entry3_1.Contains (umat 3 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.Numerical.U91.entry3_1` and `OAI.SharpPlanar.Numerical.U91.umat` (definitions bundle `OAIQ098E125` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.U91.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U91.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert91.lean (declaration OAI.SharpPlanar.Numerical.U91.entry3_1_contains)

import Mathlib
import Definitions.Def_OAIQ098E125

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical.U91
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma entry3_1_contains_e : entry3_1.Contains (umat 3 1) := by
  sorry
end SharpPlanar.Numerical.U91

end OAI
end

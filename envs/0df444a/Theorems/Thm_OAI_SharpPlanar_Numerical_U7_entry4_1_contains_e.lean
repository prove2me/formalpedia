-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_U7_entry4_1_contains_e
-- name    : OAI.SharpPlanar.Numerical.U7.entry4_1_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T18:35:08.843931+00:00
-- url     : https://prove2.me/theorems/702553af-1538-402e-8df7-44bd1e4f6240
-- title:
--   OAI.SharpPlanar.Numerical.U7.entry4_1_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.U7.entry4_1_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/WUCert7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical.U7`, with `open IntegerIntervals IntegerBasis IntegerGrid CachedData`):
--
--   ```lean
--   lemma entry4_1_contains_e : entry4_1.Contains (umat 4 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.Numerical.U7.entry4_1` and `OAI.SharpPlanar.Numerical.U7.umat` (definitions bundle `OAIQ098E125` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.U7.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U7.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert7.lean (declaration OAI.SharpPlanar.Numerical.U7.entry4_1_contains)

import Mathlib
import Definitions.Def_OAIQ098E125

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical.U7
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma entry4_1_contains_e : entry4_1.Contains (umat 4 1) := by
  sorry
end SharpPlanar.Numerical.U7

end OAI
end

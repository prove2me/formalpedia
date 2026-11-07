-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_U60_entry0_0_contains_e
-- name    : OAI.SharpPlanar.Numerical.U60.entry0_0_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T18:13:05.150075+00:00
-- url     : https://prove2.me/theorems/81febb10-3b36-499a-96f1-dbf19b12a53b
-- title:
--   OAI.SharpPlanar.Numerical.U60.entry0_0_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.U60.entry0_0_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/WUCert60.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert60.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical.U60`, with `open IntegerIntervals IntegerBasis IntegerGrid CachedData`):
--
--   ```lean
--   lemma entry0_0_contains_e : entry0_0.Contains (umat 0 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.Numerical.U60.entry0_0` and `OAI.SharpPlanar.Numerical.U60.umat` (definitions bundle `OAIQ098E125` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.U60.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U60.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert60.lean (declaration OAI.SharpPlanar.Numerical.U60.entry0_0_contains)

import Mathlib
import Definitions.Def_OAIQ098E125

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical.U60
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma entry0_0_contains_e : entry0_0.Contains (umat 0 0) := by
  sorry
end SharpPlanar.Numerical.U60

end OAI
end

-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_U19_entry4_0_contains_g
-- name    : OAI.SharpPlanar.Numerical.U19.entry4_0_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T19:26:50.093193+00:00
-- url     : https://prove2.me/theorems/7ee0177c-f824-4825-9a16-f8357dbfd56a
-- title:
--   OAI.SharpPlanar.Numerical.U19.entry4_0_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.U19.entry4_0_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/WUCert19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical.U19`, with `open IntegerIntervals IntegerBasis IntegerGrid CachedData`):
--
--   ```lean
--   lemma entry4_0_contains_g : entry4_0.Contains (umat 4 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.Numerical.U19.entry4_0` (definitions bundle `OAIQ098G362` of this split); `OAI.SharpPlanar.Numerical.U19.umat` (definitions bundle `OAIQ098G371` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.U19.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U19.wuplus_column_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert19.lean (declaration OAI.SharpPlanar.Numerical.U19.entry4_0_contains)

import Mathlib
import Definitions.Def_OAIQ098G362
import Definitions.Def_OAIQ098G371

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical.U19
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma entry4_0_contains_g : entry4_0.Contains (umat 4 0) := by
  sorry
end SharpPlanar.Numerical.U19

end OAI
end

-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm3_0_0_7_atomContains_g
-- name    : OAI.SharpPlanar.CachedData.hm3_0_0_7.atomContains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T23:44:03.810115+00:00
-- url     : https://prove2.me/theorems/ed699074-20e1-46fe-b444-a63a8f274834
-- title:
--   OAI.SharpPlanar.CachedData.hm3_0_0_7.atomContains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm3_0_0_7.atomContains` of [lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments3_0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments3_0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm3_0_0_7`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma atomContains_g : atomAnswer.Contains (fullMomentAtom false false 3 7)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.hm3_0_0_7.atomAnswer` (definitions bundle `OAIQ098G1209` of this split); `OAI.SharpPlanar.fullMomentAtom` (definitions bundle `OAIQ098G1680` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.CachedData.hm3_0_0_7.realContains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments3_0.lean (declaration OAI.SharpPlanar.CachedData.hm3_0_0_7.atomContains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1209
import Definitions.Def_OAIQ098G1680

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm3_0_0_7
lemma atomContains_g : atomAnswer.Contains (fullMomentAtom false false 3 7) := by
  sorry
end hm3_0_0_7
end SharpPlanar.CachedData

end OAI
end

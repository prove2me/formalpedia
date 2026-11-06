-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_dentry5_5_contains_e
-- name    : OAI.SharpPlanar.Numerical.dentry5_5_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:04:39.408073+00:00
-- url     : https://prove2.me/theorems/8577a5dc-8aab-436e-a485-6f3a5c260bb1
-- title:
--   OAI.SharpPlanar.Numerical.dentry5_5_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.dentry5_5_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/DEntries.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/DEntries.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical`, with `open IntegerIntervals IntegerBasis IntegerGrid CachedData`):
--
--   ```lean
--   lemma dentry5_5_contains_e : dentry5_5.Contains (S (columnVector node4 true) (node4,true))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` and `OAI.SharpPlanar.Numerical.node4` (definitions bundle `OAIQ098E000` of this split); `OAI.SharpPlanar.X` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.S` and `OAI.SharpPlanar.columnVector` (definitions bundle `OAIQ098E004` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.Numerical.dentry5_5` (definitions bundle `OAIQ098E030` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.defectminus_norm_e` and `OAI.SharpPlanar.Numerical.defectplus_norm_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/DEntries.lean (declaration OAI.SharpPlanar.Numerical.dentry5_5_contains)

import Mathlib
import Definitions.Def_OAIQ098E004
import Definitions.Def_OAIQ098E028
import Definitions.Def_OAIQ098E030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma dentry5_5_contains_e : dentry5_5.Contains (S (columnVector node4 true) (node4,true)) := by
  sorry
end SharpPlanar.Numerical

end OAI
end

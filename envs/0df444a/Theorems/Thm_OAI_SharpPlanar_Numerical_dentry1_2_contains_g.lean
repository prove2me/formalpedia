-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_dentry1_2_contains_g
-- name    : OAI.SharpPlanar.Numerical.dentry1_2_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T02:18:55.949255+00:00
-- url     : https://prove2.me/theorems/218b28a8-e13f-4ba7-bdc4-39828af0d9d1
-- title:
--   OAI.SharpPlanar.Numerical.dentry1_2_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.dentry1_2_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/DEntries.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/DEntries.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical`, with `open IntegerIntervals IntegerBasis IntegerGrid CachedData`):
--
--   ```lean
--   lemma dentry1_2_contains_g : dentry1_2.Contains (S (columnVector node4 false) (node3,false))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node`, `OAI.SharpPlanar.Numerical.node3` and `OAI.SharpPlanar.Numerical.node4` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.X` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.S` and `OAI.SharpPlanar.columnVector` (definitions bundle `OAIQ098G004` of this split); `OAI.SharpPlanar.Numerical.dentry1_2` and `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.defectminus_column_g` and `OAI.SharpPlanar.Numerical.defectplus_column_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/DEntries.lean (declaration OAI.SharpPlanar.Numerical.dentry1_2_contains)

import Mathlib
import Definitions.Def_OAIQ098G004
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma dentry1_2_contains_g : dentry1_2.Contains (S (columnVector node4 false) (node3,false)) := by
  sorry
end SharpPlanar.Numerical

end OAI
end

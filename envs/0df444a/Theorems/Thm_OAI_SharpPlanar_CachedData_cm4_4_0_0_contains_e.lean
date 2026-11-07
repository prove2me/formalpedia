-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_cm4_4_0_0_contains_e
-- name    : OAI.SharpPlanar.CachedData.cm4_4_0_0.contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T10:36:23.924126+00:00
-- url     : https://prove2.me/theorems/353a5553-e267-40e5-ac53-57f994091def
-- title:
--   OAI.SharpPlanar.CachedData.cm4_4_0_0.contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.cm4_4_0_0.contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/DMoments4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/DMoments4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.cm4_4_0_0`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma contains_e : ans.Contains (momentRuleValue quadraturePoint fejerWeight 4 4 false false)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.IntegerBasis.momentRuleValue` and `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.CachedData.cm4_4_0_0.ans` (definitions bundle `OAIQ098E026` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.dentry2_2_contains_e` and `OAI.SharpPlanar.Numerical.dentry5_2_contains_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/DMoments4.lean (declaration OAI.SharpPlanar.CachedData.cm4_4_0_0.contains)

import Mathlib
import Definitions.Def_OAIQ098E031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm4_4_0_0
lemma contains_e : ans.Contains (momentRuleValue quadraturePoint fejerWeight 4 4 false false) := by
  sorry
end cm4_4_0_0
end SharpPlanar.CachedData

end OAI
end

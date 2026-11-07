-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_check_e
-- name    : OAI.SharpPlanar.IntegerIntervals.RBox.add_check_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T10:33:30.953433+00:00
-- url     : https://prove2.me/theorems/597826e5-59ff-46c7-aa6b-b3c9672fea9c
-- title:
--   OAI.SharpPlanar.IntegerIntervals.RBox.add_check_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.RBox.add_check` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma RBox.add_check_e (a b : RBox) : a.AddCheck b (a.add b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox` and `OAI.SharpPlanar.IntegerIntervals.RBox.add` (definitions bundle `OAIQ098E017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.AddCheck` (definitions bundle `OAIQ098E026` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.CBox.add_check_e`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_e` and `OAI.SharpPlanar.IntegerIntervals.RBox.contains_add_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.RBox.add_check)

import Mathlib
import Definitions.Def_OAIQ098E026

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma RBox.add_check_e (a b : RBox) : a.AddCheck b (a.add b) := by
  sorry

end SharpPlanar.IntegerIntervals

end OAI
end

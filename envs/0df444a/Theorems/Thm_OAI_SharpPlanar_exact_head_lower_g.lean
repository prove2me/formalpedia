-- Prove2me | Theorems.Thm_OAI_SharpPlanar_exact_head_lower_g
-- name    : OAI.SharpPlanar.exact_head_lower_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T08:58:14.388897+00:00
-- url     : https://prove2.me/theorems/64ac85f6-9fa2-4a48-be00-d55733d2b68d
-- title:
--   OAI.SharpPlanar.exact_head_lower_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.exact_head_lower` of [lean/OAI/Analysis/PlanarPacking/TailHeadClose.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailHeadClose.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma exact_head_lower_g (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
--       (11:ℝ)/1000<(if a then 1 else -1)*headRational (exactData a) s
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.exactData` (definitions bundle `OAIQ098G1651` of this split); `OAI.SharpPlanar.headRational` (definitions bundle `OAIQ098G1685` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.exact_sign_tail_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailHeadClose.lean (declaration OAI.SharpPlanar.exact_head_lower)

import Mathlib
import Definitions.Def_OAIQ098G1651
import Definitions.Def_OAIQ098G1685

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma exact_head_lower_g (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    (11:ℝ)/1000<(if a then 1 else -1)*headRational (exactData a) s := by
  sorry
end SharpPlanar

end OAI
end

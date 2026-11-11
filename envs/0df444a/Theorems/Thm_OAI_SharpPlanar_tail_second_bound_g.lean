-- Prove2me | Theorems.Thm_OAI_SharpPlanar_tail_second_bound_g
-- name    : OAI.SharpPlanar.tail_second_bound_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T08:57:43.394828+00:00
-- url     : https://prove2.me/theorems/8f9a759e-f2d1-4a5c-93be-45648fe20747
-- title:
--   OAI.SharpPlanar.tail_second_bound_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.tail_second_bound` of [lean/OAI/Analysis/PlanarPacking/TailEnvelope.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailEnvelope.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma tail_second_bound_g (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
--       |tailErrorJet a 2 s| < 6/1000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.tailErrorJet` (definitions bundle `OAIQ098G1651` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.exact_sign_tail_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailEnvelope.lean (declaration OAI.SharpPlanar.tail_second_bound)

import Mathlib
import Definitions.Def_OAIQ098G1651

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma tail_second_bound_g (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    |tailErrorJet a 2 s| < 6/1000 := by
  sorry
end SharpPlanar

end OAI
end

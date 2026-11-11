-- Prove2me | Theorems.Thm_OAI_SharpPlanar_exact_sign_tail_g
-- name    : OAI.SharpPlanar.exact_sign_tail_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T08:57:40.357275+00:00
-- url     : https://prove2.me/theorems/caf1e676-a8de-4996-8744-e1fb9b8358a9
-- title:
--   OAI.SharpPlanar.exact_sign_tail_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.exact_sign_tail` of [lean/OAI/Analysis/PlanarPacking/TailSign.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailSign.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`):
--
--   ```lean
--   lemma exact_sign_tail_g (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
--       0 ≤ (if a then 1 else -1)*exactJet a 0 s
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.exactJet` (definitions bundle `OAIQ098G1651` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g` and `OAI.sharp_fourier_certificate` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailSign.lean (declaration OAI.SharpPlanar.exact_sign_tail)

import Mathlib
import Definitions.Def_OAIQ098G1651

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma exact_sign_tail_g (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 s := by
  sorry
end SharpPlanar

end OAI
end

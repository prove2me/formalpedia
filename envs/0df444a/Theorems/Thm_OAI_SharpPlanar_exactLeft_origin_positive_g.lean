-- Prove2me | Theorems.Thm_OAI_SharpPlanar_exactLeft_origin_positive_g
-- name    : OAI.SharpPlanar.exactLeft_origin_positive_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T09:00:30.501769+00:00
-- url     : https://prove2.me/theorems/116750a9-0011-4e76-8b48-a3fe35e9af6f
-- title:
--   OAI.SharpPlanar.exactLeft_origin_positive_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.exactLeft_origin_positive` of [lean/OAI/Analysis/PlanarPacking/OriginPositive.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/OriginPositive.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`):
--
--   ```lean
--   lemma exactLeft_origin_positive_g : 0<exactLeft 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.exactLeft` (definitions bundle `OAIQ098G1679` of this split); `OAI.SharpPlanar.Plane` (the published bundle `Def_PlanarPacking`).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.normalizedCandidate_fourier_g`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g` and `OAI.sharp_fourier_certificate` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/OriginPositive.lean (declaration OAI.SharpPlanar.exactLeft_origin_positive)

import Mathlib
import Definitions.Def_PlanarPacking
import Definitions.Def_OAIQ098G1679

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma exactLeft_origin_positive_g : 0<exactLeft 0 := by
  sorry
end SharpPlanar

end OAI
end

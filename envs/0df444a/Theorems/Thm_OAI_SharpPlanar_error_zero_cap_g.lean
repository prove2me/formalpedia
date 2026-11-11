-- Prove2me | Theorems.Thm_OAI_SharpPlanar_error_zero_cap_g
-- name    : OAI.SharpPlanar.error_zero_cap_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T08:58:10.747837+00:00
-- url     : https://prove2.me/theorems/2d4f98e1-62fb-4b33-8363-65d5fcbcc321
-- title:
--   OAI.SharpPlanar.error_zero_cap_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.error_zero_cap` of [lean/OAI/Analysis/PlanarPacking/SignCaps.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/SignCaps.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`):
--
--   ```lean
--   lemma error_zero_cap_g (a : Bool) {s : ℝ} (hs : 0 ≤ s) :
--       |exactJet a 0 s-tableHJet a 0 s|<4/1000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.exactJet` (definitions bundle `OAIQ098G1651` of this split); `OAI.SharpPlanar.tableHJet` (definitions bundle `OAIQ098G1695` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.exactLeft_origin_positive_g` and `OAI.SharpPlanar.halfSign_0_N1_right_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/SignCaps.lean (declaration OAI.SharpPlanar.error_zero_cap)

import Mathlib
import Definitions.Def_OAIQ098G1651
import Definitions.Def_OAIQ098G1695

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma error_zero_cap_g (a : Bool) {s : ℝ} (hs : 0 ≤ s) :
    |exactJet a 0 s-tableHJet a 0 s|<4/1000 := by
  sorry
end SharpPlanar

end OAI
end

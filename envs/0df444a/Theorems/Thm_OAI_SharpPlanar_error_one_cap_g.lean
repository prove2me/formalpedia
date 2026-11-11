-- Prove2me | Theorems.Thm_OAI_SharpPlanar_error_one_cap_g
-- name    : OAI.SharpPlanar.error_one_cap_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T08:57:54.539195+00:00
-- url     : https://prove2.me/theorems/480a8b31-cfa2-4bcb-8c3c-5e943bc8b84e
-- title:
--   OAI.SharpPlanar.error_one_cap_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.error_one_cap` of [lean/OAI/Analysis/PlanarPacking/SignCaps.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/SignCaps.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`):
--
--   ```lean
--   lemma error_one_cap_g (a : Bool) {s : ℝ} (hs : (1:ℝ)/2 ≤ s) :
--       |exactJet a 1 s-tableHJet a 1 s|<11/1000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.exactJet` (definitions bundle `OAIQ098G1651` of this split); `OAI.SharpPlanar.tableHJet` (definitions bundle `OAIQ098G1695` of this split).
--
--   **Used by.** The proof of `OAI.sharp_fourier_certificate` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/SignCaps.lean (declaration OAI.SharpPlanar.error_one_cap)

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
lemma error_one_cap_g (a : Bool) {s : ℝ} (hs : (1:ℝ)/2 ≤ s) :
    |exactJet a 1 s-tableHJet a 1 s|<11/1000 := by
  sorry
end SharpPlanar

end OAI
end

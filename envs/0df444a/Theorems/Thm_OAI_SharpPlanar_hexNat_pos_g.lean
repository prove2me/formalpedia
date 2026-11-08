-- Prove2me | Theorems.Thm_OAI_SharpPlanar_hexNat_pos_g
-- name    : OAI.SharpPlanar.hexNat_pos_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T16:40:57.047447+00:00
-- url     : https://prove2.me/theorems/595a356f-ab7b-4672-afd8-a5b1a11b6d1f
-- title:
--   OAI.SharpPlanar.hexNat_pos_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.hexNat_pos` of [lean/OAI/Analysis/PlanarPacking/HexLattice.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/HexLattice.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma hexNat_pos_g {v : ℤ×ℤ} (hv : v≠0) : 0<hexNat v
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.hexNat` (definitions bundle `OAIQ098G013` of this split).
--
--   **Used by.** The definitions bundle `OAIQ098G1687` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/HexLattice.lean (declaration OAI.SharpPlanar.hexNat_pos)

import Mathlib
import Definitions.Def_OAIQ098G013

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma hexNat_pos_g {v : ℤ×ℤ} (hv : v≠0) : 0<hexNat v := by
  sorry
end SharpPlanar

end OAI
end

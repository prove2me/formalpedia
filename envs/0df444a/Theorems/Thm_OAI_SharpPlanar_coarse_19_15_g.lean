-- Prove2me | Theorems.Thm_OAI_SharpPlanar_coarse_19_15_g
-- name    : OAI.SharpPlanar.coarse_19_15_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T20:55:19.894929+00:00
-- url     : https://prove2.me/theorems/7d781b45-ab86-4d71-a72c-d1d915cb14ac
-- title:
--   OAI.SharpPlanar.coarse_19_15_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.coarse_19_15` of [lean/OAI/Analysis/PlanarPacking/Certificate/CoarseBound19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/CoarseBound19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis`):
--
--   ```lean
--   lemma coarse_19_15_g : sharpTaylor 15 19/((Nat.factorial 15):ℝ)≤(88441022552632104701542875:ℝ)/1000000000000000000000000000000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.sharpTaylor` (definitions bundle `OAIQ098G1690` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein19.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein19.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein19.N1_left.bound_g` and `OAI.SharpPlanar.Bernstein19.N1_right.bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/CoarseBound19.lean (declaration OAI.SharpPlanar.coarse_19_15)

import Mathlib
import Definitions.Def_OAIQ098G1690

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma coarse_19_15_g : sharpTaylor 15 19/((Nat.factorial 15):ℝ)≤(88441022552632104701542875:ℝ)/1000000000000000000000000000000 := by
  sorry
end SharpPlanar

end OAI
end

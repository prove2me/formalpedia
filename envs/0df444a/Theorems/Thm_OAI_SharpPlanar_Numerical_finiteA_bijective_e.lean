-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_finiteA_bijective_e
-- name    : OAI.SharpPlanar.Numerical.finiteA_bijective_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T04:44:48.53379+00:00
-- url     : https://prove2.me/theorems/c52d20d6-1330-444e-abc4-4e23f28e26cf
-- title:
--   OAI.SharpPlanar.Numerical.finiteA_bijective_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.finiteA_bijective` of [lean/OAI/Analysis/PlanarPacking/FiniteFull.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteFull.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical`):
--
--   ```lean
--   lemma finiteA_bijective_e (neg : Bool) : Function.Bijective (finiteA neg)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.L1Finite` (definitions bundle `OAIQ098E004` of this split); `OAI.SharpPlanar.Numerical.FiniteIndex` (definitions bundle `OAIQ098E007` of this split); `OAI.SharpPlanar.Numerical.finiteA` (definitions bundle `OAIQ098E010` of this split).
--
--   **Used by.** The definitions bundle `OAIQ098E127` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteFull.lean (declaration OAI.SharpPlanar.Numerical.finiteA_bijective)

import Mathlib
import Definitions.Def_OAIQ098E010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical
lemma finiteA_bijective_e (neg : Bool) : Function.Bijective (finiteA neg) := by
  sorry
end SharpPlanar.Numerical

end OAI
end

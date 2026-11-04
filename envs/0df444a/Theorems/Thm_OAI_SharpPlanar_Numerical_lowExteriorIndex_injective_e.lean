-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_lowExteriorIndex_injective_e
-- name    : OAI.SharpPlanar.Numerical.lowExteriorIndex_injective_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T05:47:01.807873+00:00
-- url     : https://prove2.me/theorems/8cab9f6f-170d-4a7d-bdb3-0c21339990de
-- title:
--   OAI.SharpPlanar.Numerical.lowExteriorIndex_injective_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.lowExteriorIndex_injective` of [lean/OAI/Analysis/PlanarPacking/Indices.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma lowExteriorIndex_injective_e : Function.Injective lowExteriorIndex
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098E000` of this split); `OAI.SharpPlanar.Numerical.lowExteriorIndex` (definitions bundle `OAIQ098E011` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.finiteA_bijective_e`, `OAI.SharpPlanar.Numerical.interpolation_exists_unique_e`, `OAI.SharpPlanar.error_large_cap_e`, `OAI.SharpPlanar.error_one_cap_e`, `OAI.SharpPlanar.error_two_cap_e`, `OAI.SharpPlanar.error_zero_cap_e`, `OAI.SharpPlanar.exact_head_lower_e` and `OAI.SharpPlanar.tail_second_bound_e` and the definitions bundle `OAIQ098E111` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean (declaration OAI.SharpPlanar.Numerical.lowExteriorIndex_injective)

import Mathlib
import Definitions.Def_OAIQ098E011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical

open scoped BigOperators
lemma lowExteriorIndex_injective_e : Function.Injective lowExteriorIndex := by
  sorry
end SharpPlanar.Numerical

end OAI
end

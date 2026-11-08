-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_injective_g
-- name    : OAI.SharpPlanar.Numerical.finiteIndex_injective_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:08:56.280613+00:00
-- url     : https://prove2.me/theorems/6f0fc42c-1dee-4e52-b458-9bbb008cac3c
-- title:
--   OAI.SharpPlanar.Numerical.finiteIndex_injective_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.finiteIndex_injective` of [lean/OAI/Analysis/PlanarPacking/Indices.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma finiteIndex_injective_g : Function.Injective finiteIndex
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.Numerical.FiniteIndex` and `OAI.SharpPlanar.Numerical.finiteIndex` (definitions bundle `OAIQ098G007` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.interpolation_exists_unique_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g`, `OAI.SharpPlanar.tableList_discard_g`, `OAI.SharpPlanar.table_coeff_mass_g` and `OAI.SharpPlanar.tail_second_bound_g` and the definitions bundle `OAIQ098G010` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean (declaration OAI.SharpPlanar.Numerical.finiteIndex_injective)

import Mathlib
import Definitions.Def_OAIQ098G007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical

open scoped BigOperators
lemma finiteIndex_injective_g : Function.Injective finiteIndex := by
  sorry
end SharpPlanar.Numerical

end OAI
end

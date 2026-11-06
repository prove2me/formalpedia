-- Prove2me | Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_norm_e
-- name    : OAI.SharpPlanar.finiteEmbedding_norm_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T04:46:44.338063+00:00
-- url     : https://prove2.me/theorems/be709313-bd04-43ff-9fea-915bf37e7a7e
-- title:
--   OAI.SharpPlanar.finiteEmbedding_norm_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.finiteEmbedding_norm` of [lean/OAI/Analysis/PlanarPacking/FiniteCoordinates.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteCoordinates.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ENNReal`):
--
--   ```lean
--   lemma finiteEmbedding_norm_e (x : L1Finite ι) : ‖finiteEmbedding e x‖ = ‖x‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098E000` of this split); `OAI.SharpPlanar.X` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.L1Finite` (definitions bundle `OAIQ098E004` of this split); `OAI.SharpPlanar.finiteEmbedding` (definitions bundle `OAIQ098E010` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.finiteA_bijective_e`, `OAI.SharpPlanar.Numerical.interpolation_exists_unique_e`, `OAI.SharpPlanar.error_large_cap_e`, `OAI.SharpPlanar.error_one_cap_e`, `OAI.SharpPlanar.error_two_cap_e`, `OAI.SharpPlanar.error_zero_cap_e`, `OAI.SharpPlanar.exact_head_lower_e`, `OAI.SharpPlanar.table_coeff_mass_e` and `OAI.SharpPlanar.tail_second_bound_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteCoordinates.lean (declaration OAI.SharpPlanar.finiteEmbedding_norm)

import Mathlib
import Definitions.Def_OAIQ098E010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
include he in
lemma finiteEmbedding_norm_e (x : L1Finite ι) : ‖finiteEmbedding e x‖ = ‖x‖ := by
  sorry
end
end SharpPlanar

end OAI
end

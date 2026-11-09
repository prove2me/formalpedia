-- Prove2me | Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_g
-- name    : OAI.SharpPlanar.l1Finite_norm_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T09:09:36.710074+00:00
-- url     : https://prove2.me/theorems/c3e2b5d0-bd64-48c8-966c-0387a8b38e4f
-- title:
--   OAI.SharpPlanar.l1Finite_norm_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.l1Finite_norm` of [lean/OAI/Analysis/PlanarPacking/MatrixL1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/MatrixL1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma l1Finite_norm_g (x : L1Finite ι) : ‖x‖ = ∑ i, |x i|
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.L1Finite` (definitions bundle `OAIQ098G004` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.defectminus_lt_one_g`, `OAI.SharpPlanar.Numerical.defectplus_lt_one_g`, `OAI.SharpPlanar.Numerical.finiteA_bijective_g`, `OAI.SharpPlanar.Numerical.interpolation_exists_unique_g`, `OAI.SharpPlanar.Numerical.signedVU_norm_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g`, `OAI.SharpPlanar.finiteEmbedding_bound_g`, `OAI.SharpPlanar.finiteRestriction_bound_g`, `OAI.SharpPlanar.residual_finite_bound_g`, `OAI.SharpPlanar.table_coeff_mass_g` and `OAI.SharpPlanar.tail_second_bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/MatrixL1.lean (declaration OAI.SharpPlanar.l1Finite_norm)

import Mathlib
import Definitions.Def_OAIQ098G004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
lemma l1Finite_norm_g (x : L1Finite ι) : ‖x‖ = ∑ i, |x i| := by
  sorry

end

end SharpPlanar

end OAI
end

-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_defectplus_column_g
-- name    : OAI.SharpPlanar.Numerical.defectplus_column_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-08T09:22:54.511815+00:00
-- url     : https://prove2.me/theorems/8885c538-7e2b-465f-a601-0924aa3ec152
-- title:
--   OAI.SharpPlanar.Numerical.defectplus_column_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.defectplus_column` of [lean/OAI/Analysis/PlanarPacking/Certificate/WCertificates.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WCertificates.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma defectplus_column_g (j : Fin 6) : ∑ i, |((1-Wplus*Aplus) i j)| < (1:ℝ)/1000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Numerical.Aplus` and `OAI.SharpPlanar.Numerical.Wplus` (definitions bundle `OAIQ098G005` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.defectplus_lt_one_g`, `OAI.SharpPlanar.Numerical.finiteA_bijective_g`, `OAI.SharpPlanar.Numerical.interpolation_exists_unique_g`, `OAI.SharpPlanar.Numerical.signedVU_norm_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g` and `OAI.SharpPlanar.tail_second_bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WCertificates.lean (declaration OAI.SharpPlanar.Numerical.defectplus_column)

import Mathlib
import Definitions.Def_OAIQ098G005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical
open scoped BigOperators
lemma defectplus_column_g (j : Fin 6) : ∑ i, |((1-Wplus*Aplus) i j)| < (1:ℝ)/1000 := by
  sorry
end SharpPlanar.Numerical

end OAI
end

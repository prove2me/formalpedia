-- Prove2me | Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_g
-- name    : OAI.SharpPlanar.lambdaCap_nonneg_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T20:51:12.67613+00:00
-- url     : https://prove2.me/theorems/6f846a7d-664f-4b03-9677-65d9370fb074
-- title:
--   OAI.SharpPlanar.lambdaCap_nonneg_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.lambdaCap_nonneg` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerBasis`):
--
--   ```lean
--   lemma lambdaCap_nonneg_g (j : Fin 7) : 0 ≤ lambdaCap j
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.lambdaCap` (definitions bundle `OAIQ098G362` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.interpolation_exists_unique_g`, `OAI.SharpPlanar.atomL_nonneg_g`, `OAI.SharpPlanar.atomicEnvelope_le_rat_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g`, `OAI.SharpPlanar.halfSign_0_N1_right_g`, `OAI.SharpPlanar.kernelMoment_endpoint_bound_g`, `OAI.SharpPlanar.kernelMoment_segment_bound_g`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g`, `OAI.SharpPlanar.pieceL_le_intCap_g`, `OAI.SharpPlanar.pieceL_nonneg_g`, `OAI.SharpPlanar.rowTable_le_g`, `OAI.SharpPlanar.segmentEnvelope_integral_bound_g`, `OAI.SharpPlanar.sharp_S_tail_g`, `OAI.SharpPlanar.tail_second_bound_g`, `OAI.SharpPlanar.transformEnvelope_le_rat_g` and `OAI.sharp_fourier_certificate` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.lambdaCap_nonneg)

import Mathlib
import Definitions.Def_OAIQ098G362

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis

lemma lambdaCap_nonneg_g (j : Fin 7) : 0 ≤ lambdaCap j := by
  sorry

end SharpPlanar

end OAI
end

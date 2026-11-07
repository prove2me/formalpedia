-- Prove2me | Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_e
-- name    : OAI.SharpPlanar.densityCap_nonneg_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T22:20:43.799036+00:00
-- url     : https://prove2.me/theorems/f81e1a48-07c2-489f-a379-5fb647ae4125
-- title:
--   OAI.SharpPlanar.densityCap_nonneg_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.densityCap_nonneg` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerBasis`):
--
--   ```lean
--   lemma densityCap_nonneg_e (j : Fin 6) : 0 ≤ densityCap j
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerBasis.densityCap` (definitions bundle `OAIQ098E126` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.finiteA_bijective_e`, `OAI.SharpPlanar.Numerical.interpolation_exists_unique_e`, `OAI.SharpPlanar.directEnvelope_le_rat_e`, `OAI.SharpPlanar.direct_spectral_bound_e`, `OAI.SharpPlanar.error_large_cap_e`, `OAI.SharpPlanar.error_one_cap_e`, `OAI.SharpPlanar.error_two_cap_e`, `OAI.SharpPlanar.error_zero_cap_e`, `OAI.SharpPlanar.exact_head_lower_e`, `OAI.SharpPlanar.halfSign_0_N1_right_e`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_e`, `OAI.SharpPlanar.sharp_integral_piece_bound_e`, `OAI.SharpPlanar.table_jet_sharp_e`, `OAI.SharpPlanar.tail_second_bound_e`, `OAI.SharpPlanar.transformEnvelope_le_rat_e`, `OAI.SharpPlanar.transformEnvelope_nonneg_e` and `OAI.sharp_fourier_certificate` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.densityCap_nonneg)

import Mathlib
import Definitions.Def_OAIQ098E126

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

lemma densityCap_nonneg_e (j : Fin 6) : 0 ≤ densityCap j := by
  sorry

end SharpPlanar

end OAI
end

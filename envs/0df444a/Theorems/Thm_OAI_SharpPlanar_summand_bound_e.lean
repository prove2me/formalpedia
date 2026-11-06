-- Prove2me | Theorems.Thm_OAI_SharpPlanar_summand_bound_e
-- name    : OAI.SharpPlanar.summand_bound_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:59:00.972821+00:00
-- url     : https://prove2.me/theorems/ea9e1b65-2e7f-49a8-bf78-984f6eccdabb
-- title:
--   OAI.SharpPlanar.summand_bound_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.summand_bound` of [lean/OAI/Analysis/PlanarPacking/Cardinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`):
--
--   ```lean
--   lemma summand_bound_e (x : X) (n : Node) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
--       ‖(x (n, false) : ℂ) * u n.val j t + (x (n, true) : ℂ) * v n.val j t‖ ≤
--         densityBound * (|x (n, false)| + |x (n, true)|)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` and `OAI.SharpPlanar.residues` (definitions bundle `OAIQ098E000` of this split); `OAI.SharpPlanar.X`, `OAI.SharpPlanar.u` and `OAI.SharpPlanar.v` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.densityBound` (definitions bundle `OAIQ098E002` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Scoords_add_e`, `OAI.SharpPlanar.Scoords_mem_e`, `OAI.SharpPlanar.Slinear_bound_e`, `OAI.SharpPlanar.continuousOn_density_e`, `OAI.SharpPlanar.directDensity_tsum_e`, `OAI.SharpPlanar.direct_basis_integral_bound_e`, `OAI.SharpPlanar.error_large_cap_e`, `OAI.SharpPlanar.error_one_cap_e`, `OAI.SharpPlanar.error_two_cap_e`, `OAI.SharpPlanar.error_zero_cap_e`, `OAI.SharpPlanar.exactLeft_origin_positive_e`, `OAI.SharpPlanar.exact_sign_tail_e`, `OAI.SharpPlanar.halfSign_0_N1_right_e`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_e`, `OAI.SharpPlanar.transformedJets_summable_e` and `OAI.sharp_fourier_certificate` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean (declaration OAI.SharpPlanar.summand_bound)

import Mathlib
import Definitions.Def_OAIQ098E002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma summand_bound_e (x : X) (n : Node) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(x (n, false) : ℂ) * u n.val j t + (x (n, true) : ℂ) * v n.val j t‖ ≤
      densityBound * (|x (n, false)| + |x (n, true)|) := by
  sorry

end SharpPlanar

end OAI
end

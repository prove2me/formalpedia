-- Prove2me | Theorems.Thm_OAI_SharpPlanar_complexBasisMoment_ofReal_e
-- name    : OAI.SharpPlanar.complexBasisMoment_ofReal_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T10:33:54.231602+00:00
-- url     : https://prove2.me/theorems/7d83dd37-5176-4b07-8b9c-afa70439043a
-- title:
--   OAI.SharpPlanar.complexBasisMoment_ofReal_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.complexBasisMoment_ofReal` of [lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis`):
--
--   ```lean
--   lemma complexBasisMoment_ofReal_e (d e : Bool) (n j m : ℕ) (t : ℝ) :
--       complexBasisMoment d e n j m t = basisMoment d e n j m t
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.complexBasisMoment` and `OAI.SharpPlanar.IntegerBasis.basisMoment` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.K_column_contains_e` and `OAI.SharpPlanar.basis_rule_value_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean (declaration OAI.SharpPlanar.complexBasisMoment_ofReal)

import Mathlib
import Definitions.Def_OAIQ098E018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis

lemma complexBasisMoment_ofReal_e (d e : Bool) (n j m : ℕ) (t : ℝ) :
    complexBasisMoment d e n j m t = basisMoment d e n j m t := by
  sorry

end SharpPlanar

end OAI
end

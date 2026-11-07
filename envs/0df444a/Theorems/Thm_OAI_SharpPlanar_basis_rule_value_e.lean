-- Prove2me | Theorems.Thm_OAI_SharpPlanar_basis_rule_value_e
-- name    : OAI.SharpPlanar.basis_rule_value_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T10:33:53.523+00:00
-- url     : https://prove2.me/theorems/6d397e99-35af-43c2-8a93-b6d065f7ab6f
-- title:
--   OAI.SharpPlanar.basis_rule_value_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.basis_rule_value` of [lean/OAI/Analysis/PlanarPacking/BasisQuadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisQuadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma basis_rule_value_e (n m : ℕ) (d e : Bool) :
--       (∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val) =
--         momentRuleValue quadraturePoint fejerWeight n m d e
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.complexBasisMoment`, `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.pieceRule`, `OAI.SharpPlanar.IntegerBasis.momentRuleValue` and `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Numerical.K_column_contains_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisQuadrature.lean (declaration OAI.SharpPlanar.basis_rule_value)

import Mathlib
import Definitions.Def_OAIQ098E018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid

lemma basis_rule_value_e (n m : ℕ) (d e : Bool) :
    (∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val) =
      momentRuleValue quadraturePoint fejerWeight n m d e := by
  sorry

end SharpPlanar

end OAI
end

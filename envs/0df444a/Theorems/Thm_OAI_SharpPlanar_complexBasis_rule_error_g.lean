-- Prove2me | Theorems.Thm_OAI_SharpPlanar_complexBasis_rule_error_g
-- name    : OAI.SharpPlanar.complexBasis_rule_error_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:11:51.436986+00:00
-- url     : https://prove2.me/theorems/390f6294-2f66-4f83-87ca-6f5e06bbb1ff
-- title:
--   OAI.SharpPlanar.complexBasis_rule_error_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.complexBasis_rule_error` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`, `open MeasureTheory Set`, `open scoped BigOperators`, `open MeasureTheory`):
--
--   ```lean
--   lemma complexBasis_rule_error_g {n m : ℕ} (hn : n ≤ 100) (hm : m ≤ 100) (d e : Bool) :
--       ‖(∑ j : Fin 6, pieceIntegral (complexBasisMoment d e n j.val m) j.val)-
--         ∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val‖ < 1/10^22
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.complexBasisMoment`, `OAI.SharpPlanar.pieceIntegral` and `OAI.SharpPlanar.pieceRule` (definitions bundle `OAIQ098G072` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Numerical.K_column_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.complexBasis_rule_error)

import Mathlib
import Definitions.Def_OAIQ098G072

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory

lemma complexBasis_rule_error_g {n m : ℕ} (hn : n ≤ 100) (hm : m ≤ 100) (d e : Bool) :
    ‖(∑ j : Fin 6, pieceIntegral (complexBasisMoment d e n j.val m) j.val)-
      ∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val‖ < 1/10^22 := by
  sorry

end SharpPlanar

end OAI
end

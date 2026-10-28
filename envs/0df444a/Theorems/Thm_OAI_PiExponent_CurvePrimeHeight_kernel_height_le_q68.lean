-- Prove2me | Theorems.Thm_OAI_PiExponent_CurvePrimeHeight_kernel_height_le_q68
-- name    : OAI.PiExponent.CurvePrimeHeight.kernel_height_le_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:12:43.03287+00:00
-- url     : https://prove2.me/theorems/16db8f7b-7ae7-4ba4-bea9-9e285920b9ed
-- title:
--   OAI.PiExponent.CurvePrimeHeight.kernel_height_le_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.CurvePrimeHeight.kernel_height_le` of [lean/OAI/NumberTheory/PiExponent/Geometry/CurvePrimeHeight.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurvePrimeHeight.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.CurvePrimeHeight`):
--
--   ```lean
--   theorem kernel_height_le_q68 {n : ℕ} (z : Fin n → E)
--       (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
--       (htrdeg : Algebra.trdeg F E = 1) :
--       (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height ≤ (n : ℕ∞)
--   ```
--
--   **Used by.** The proof of `OAI.PiExponent.CurveInequality.weighted_curve_inequality_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurvePrimeHeight.lean (declaration OAI.PiExponent.CurvePrimeHeight.kernel_height_le)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurvePrimeHeight

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem kernel_height_le_q68 {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height ≤ (n : ℕ∞) := by
  sorry

end PiExponent.CurvePrimeHeight

end OAI
end

-- Prove2me | Theorems.Thm_OAI_PiExponentJets_PolynomialLocalResidueResolution_exists_regularParameters_actual_height_q68
-- name    : OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:13:27.826611+00:00
-- url     : https://prove2.me/theorems/ae74a3ee-836a-4002-bcd3-38639ea4ea82
-- title:
--   OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height` of [lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalRegularParameters.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalRegularParameters.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.PolynomialLocalResidueResolution`):
--
--   ```lean
--   theorem exists_regularParameters_actual_height_q68 :
--       ∃ h : ℕ, Q.height = (h : ℕ∞) ∧
--         ∃ xs : List (Localization.AtPrime Q),
--           xs.length = h ∧ RingTheory.Sequence.IsRegular (Localization.AtPrime Q) xs ∧
--           Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime Q)
--   ```
--
--   **Used by.** The proof of `OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalRegularParameters.lean (declaration OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

theorem exists_regularParameters_actual_height_q68 :
    ∃ h : ℕ, Q.height = (h : ℕ∞) ∧
      ∃ xs : List (Localization.AtPrime Q),
        xs.length = h ∧ RingTheory.Sequence.IsRegular (Localization.AtPrime Q) xs ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  sorry

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

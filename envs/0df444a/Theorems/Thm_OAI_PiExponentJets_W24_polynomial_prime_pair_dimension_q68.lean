-- Prove2me | Theorems.Thm_OAI_PiExponentJets_W24_polynomial_prime_pair_dimension_q68
-- name    : OAI.PiExponentJets.W24.polynomial_prime_pair_dimension_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:13:50.013518+00:00
-- url     : https://prove2.me/theorems/3d789efb-a96f-4fae-a1cc-a3fe3ee52599
-- title:
--   OAI.PiExponentJets.W24.polynomial_prime_pair_dimension_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.W24.polynomial_prime_pair_dimension` of [lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialPrimeDimension.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialPrimeDimension.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.W24`):
--
--   ```lean
--   theorem polynomial_prime_pair_dimension_q68 (hPQ : P ≤ Q) :
--       ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) +
--         ringKrullDim (MvPolynomial σ k ⧸ Q) = ringKrullDim (MvPolynomial σ k ⧸ P)
--   ```
--
--   **Used by.** The proof of `OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialPrimeDimension.lean (declaration OAI.PiExponentJets.W24.polynomial_prime_pair_dimension)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W24

variable (k σ : Type*) [Field k] [Finite σ]
variable (P Q : Ideal (MvPolynomial σ k)) [P.IsPrime] [Q.IsPrime]

theorem polynomial_prime_pair_dimension_q68 (hPQ : P ≤ Q) :
    ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) +
      ringKrullDim (MvPolynomial σ k ⧸ Q) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  sorry

end PiExponentJets.W24

end

end OAI
end

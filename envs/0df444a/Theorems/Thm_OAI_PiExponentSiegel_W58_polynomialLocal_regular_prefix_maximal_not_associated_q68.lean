-- Prove2me | Theorems.Thm_OAI_PiExponentSiegel_W58_polynomialLocal_regular_prefix_maximal_not_associated_q68
-- name    : OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:14:35.909932+00:00
-- url     : https://prove2.me/theorems/e746723b-3f04-4355-a1b7-aa020099596a
-- title:
--   OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularParameterSelection.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularParameterSelection.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentSiegel.W58`, with `open IsLocalRing RingTheory.Sequence CategoryTheory CategoryTheory.Abelian`):
--
--   ```lean
--   theorem polynomialLocal_regular_prefix_maximal_not_associated_q68
--       (rs : List (Localization.AtPrime P))
--       (hreg : IsRegular (Localization.AtPrime P) rs)
--       (hshort : (rs.length : ℕ∞) < P.height) :
--       ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime P))
--         (Localization.AtPrime P ⧸ Ideal.ofList rs)
--   ```
--
--   **Used by.** The proof of `OAI.PiExponent.localIsolatedBezout_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularParameterSelection.lean (declaration OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
open IsLocalRing RingTheory.Sequence CategoryTheory CategoryTheory.Abelian
namespace PiExponentSiegel.W58

variable (k : Type u) [Field k] (n : ℕ)
variable (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]

theorem polynomialLocal_regular_prefix_maximal_not_associated_q68
    (rs : List (Localization.AtPrime P))
    (hreg : IsRegular (Localization.AtPrime P) rs)
    (hshort : (rs.length : ℕ∞) < P.height) :
    ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P ⧸ Ideal.ofList rs) := by
  sorry

end PiExponentSiegel.W58

end

end OAI
end

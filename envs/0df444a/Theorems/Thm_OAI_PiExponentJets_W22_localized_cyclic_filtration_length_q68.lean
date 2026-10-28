-- Prove2me | Theorems.Thm_OAI_PiExponentJets_W22_localized_cyclic_filtration_length_q68
-- name    : OAI.PiExponentJets.W22.localized_cyclic_filtration_length_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:13:50.909497+00:00
-- url     : https://prove2.me/theorems/bbdbd4f8-e56b-4709-b8d2-f70fd53c0c7a
-- title:
--   OAI.PiExponentJets.W22.localized_cyclic_filtration_length_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.W22.localized_cyclic_filtration_length` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedFiltrationLength.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedFiltrationLength.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.W22`, with `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem localized_cyclic_filtration_length_q68
--       (I Q : Ideal R) [Q.IsPrime] (hQ : Q ∈ I.minimalPrimes)
--       (J : ℕ → Ideal R) (hmono : ∀ i, J i ≤ J (i + 1))
--       (hstart : J 0 = I) (n : ℕ) (hend : J n = ⊤)
--       (f : ℕ → R)
--       (hstep : ∀ i < n, J (i + 1) = J i ⊔ Ideal.span {f i})
--       (hprime : ∀ i < n, ((J i).colon {f i}).IsPrime) :
--       Module.length (Localization.AtPrime Q)
--         (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) =
--         ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0
--   ```
--
--   **Used by.** The proofs of `OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68`, `OAI.PiExponentJets.W22.component_multiplicity_sum_bound_q68`, `OAI.PiExponentJets.W22.homogeneous_local_regular_bezout_q68` and `OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedFiltrationLength.lean (declaration OAI.PiExponentJets.W22.localized_cyclic_filtration_length)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

theorem localized_cyclic_filtration_length_q68
    (I Q : Ideal R) [Q.IsPrime] (hQ : Q ∈ I.minimalPrimes)
    (J : ℕ → Ideal R) (hmono : ∀ i, J i ≤ J (i + 1))
    (hstart : J 0 = I) (n : ℕ) (hend : J n = ⊤)
    (f : ℕ → R)
    (hstep : ∀ i < n, J (i + 1) = J i ⊔ Ideal.span {f i})
    (hprime : ∀ i < n, ((J i).colon {f i}).IsPrime) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) =
      ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0 := by
  sorry

end PiExponentJets.W22

end OAI
end

-- Prove2me | Theorems.Thm_OAI_PiExponentJets_W28_LocalIntersection_exists_cyclic_filtration_all_local_counts_q68
-- name    : OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:14:12.810626+00:00
-- url     : https://prove2.me/theorems/5da57765-73de-4aa1-9c36-a743246b90a5
-- title:
--   OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionPrimeFiltration.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionPrimeFiltration.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.W28.LocalIntersection`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_cyclic_filtration_all_local_counts_q68 :
--       ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
--         (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
--         (∀ i < n, ((J i).colon {f i}).IsPrime ∧
--           J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
--         ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
--           Module.length (Localization.AtPrime P)
--             (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
--               (algebraMap A (Localization.AtPrime P))) =
--             ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0
--   ```
--
--   **Used by.** The proof of `OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionPrimeFiltration.lean (declaration OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem exists_cyclic_filtration_all_local_counts_q68 :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
      (∀ i < n, ((J i).colon {f i}).IsPrime ∧
        J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
      ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P))) =
          ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0 := by
  sorry

end PiExponentJets.W28.LocalIntersection

end OAI
end

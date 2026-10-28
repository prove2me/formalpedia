-- Prove2me | Theorems.Thm_OAI_Lech_LinearNormalization_exists_linear_normalization
-- name    : OAI.Lech.LinearNormalization.exists_linear_normalization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:03:26.549575+00:00
-- url     : https://prove2.me/theorems/74884151-db0c-4361-8ade-65a513c67a28
-- title:
--   OAI.Lech.LinearNormalization.exists_linear_normalization: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.LinearNormalization`, with `open MvPolynomial`):
--
--   ```lean
--   theorem exists_linear_normalization [Nontrivial A] [Infinite k]
--       (G : ℕ → Submodule k A) [GradedAlgebra G] {N : ℕ}
--       (x : Fin N → A) (hx : ∀ i,x i ∈ G 1) :
--       ∃ s : ℕ, s ≤ N ∧ ∃ z : Fin s → A,
--         (∀ j,z j ∈ Submodule.span k (Set.range x)) ∧
--         Function.Injective (aeval (R:=k) z) ∧
--         (∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (x i))
--   ```
--
--   **Used by.** The proof of `OAI.Lech.MinimalReduction.exists_reduction` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPolynomial
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

theorem exists_linear_normalization [Nontrivial A] [Infinite k]
    (G : ℕ → Submodule k A) [GradedAlgebra G] {N : ℕ}
    (x : Fin N → A) (hx : ∀ i,x i ∈ G 1) :
    ∃ s : ℕ, s ≤ N ∧ ∃ z : Fin s → A,
      (∀ j,z j ∈ Submodule.span k (Set.range x)) ∧
      Function.Injective (aeval (R:=k) z) ∧
      (∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (x i)) := by
  sorry

end Lech.LinearNormalization

end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_Lech_null_projector_contractible_splitting
-- name    : OAI.Lech.null_projector_contractible_splitting
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:06:30.694188+00:00
-- url     : https://prove2.me/theorems/623db646-90cc-4a7f-b58d-b94182433f28
-- title:
--   OAI.Lech.null_projector_contractible_splitting: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`):
--
--   ```lean
--   lemma null_projector_contractible_splitting
--       (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : F ⟶ F)
--       (hq : q ≫ q = q) (hn : Homotopy q 0) :
--       ∃ (G K : CochainComplex (ModuleCat.{u} R) ℤ)
--         (i : G ⟶ F) (r : F ⟶ G) (a : K ⟶ F) (b : F ⟶ K),
--         i ≫ r = 𝟙 G ∧ a ≫ b = 𝟙 K ∧ b ≫ a = q ∧
--         r ≫ i + b ≫ a = 𝟙 F ∧ i ≫ b = 0 ∧ a ≫ r = 0 ∧
--         Nonempty (HomotopyEquiv F G)
--   ```
--
--   **Used by.** The proof of `OAI.Lech.nonminimal_complex_reduction` of this split imports it.
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
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]

omit [IsLocalRing R] in
lemma null_projector_contractible_splitting
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : F ⟶ F)
    (hq : q ≫ q = q) (hn : Homotopy q 0) :
    ∃ (G K : CochainComplex (ModuleCat.{u} R) ℤ)
      (i : G ⟶ F) (r : F ⟶ G) (a : K ⟶ F) (b : F ⟶ K),
      i ≫ r = 𝟙 G ∧ a ≫ b = 𝟙 K ∧ b ≫ a = q ∧
      r ≫ i + b ≫ a = 𝟙 F ∧ i ≫ b = 0 ∧ a ≫ r = 0 ∧
      Nonempty (HomotopyEquiv F G) := by
  sorry
end Lech

end

end OAI
end

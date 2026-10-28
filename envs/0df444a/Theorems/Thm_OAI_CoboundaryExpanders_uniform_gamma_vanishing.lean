-- Prove2me | Theorems.Thm_OAI_CoboundaryExpanders_uniform_gamma_vanishing
-- name    : OAI.CoboundaryExpanders.uniform_gamma_vanishing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:29:03.102973+00:00
-- url     : https://prove2.me/theorems/5b0d5dda-710c-4c29-9719-098910076fdc
-- title:
--   OAI.CoboundaryExpanders.uniform_gamma_vanishing: intermediate lemma from OpenAI, Bounded-degree coboundary expanders in every dimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoboundaryExpanders.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Bounded-degree coboundary expanders in every dimension*, OpenAI Math Release, September 24, 2026, result family 177, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoboundaryExpanders.uniform_gamma_vanishing` of [lean/OAI/Combinatorics/Coboundary/Coboundary/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Coboundary/Coboundary/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoboundaryExpanders`, with `open CategoryTheory CategoryTheory.Limits`, `open Construction`):
--
--   ```lean
--   theorem uniform_gamma_vanishing (N : ℕ) :
--       ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Odd p → Q < p →
--         ∀ j : ℕ, 0 < j → ∀ a : ℕ, 2*j+2 ≤ a → a ≤ N →
--           ∀ m : ℕ, 1 ≤ m →
--             IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoboundaryExpanders.Construction.Gamma` and `OAI.CoboundaryExpanders.Construction.R` (definitions bundle `OAIQ3Cb000` of this split).
--
--   **Used by.** The proof of `OAI.CoboundaryExpanders.main` of this split imports it.
-- source:
--   OpenAI, Bounded-degree coboundary expanders in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 177; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Coboundary/Coboundary/Main.lean (declaration OAI.CoboundaryExpanders.uniform_gamma_vanishing)

import Mathlib
import Definitions.Def_OAIQ3Cb000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders
open Construction

theorem uniform_gamma_vanishing (N : ℕ) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Odd p → Q < p →
      ∀ j : ℕ, 0 < j → ∀ a : ℕ, 2*j+2 ≤ a → a ≤ N →
        ∀ m : ℕ, 1 ≤ m →
          IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j) := by
  sorry

end CoboundaryExpanders

end

end OAI
end

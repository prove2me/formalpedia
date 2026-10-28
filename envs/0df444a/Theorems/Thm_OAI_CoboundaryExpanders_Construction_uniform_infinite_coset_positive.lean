-- Prove2me | Theorems.Thm_OAI_CoboundaryExpanders_Construction_uniform_infinite_coset_positive
-- name    : OAI.CoboundaryExpanders.Construction.uniform_infinite_coset_positive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:29:11.771299+00:00
-- url     : https://prove2.me/theorems/20f2f800-4186-4e2b-9a33-a9f7b89b682a
-- title:
--   OAI.CoboundaryExpanders.Construction.uniform_infinite_coset_positive: intermediate lemma from OpenAI, Bounded-degree coboundary expanders in every dimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoboundaryExpanders.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Bounded-degree coboundary expanders in every dimension*, OpenAI Math Release, September 24, 2026, result family 177, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoboundaryExpanders.Construction.uniform_infinite_coset_positive` of [lean/OAI/Combinatorics/Coboundary/Coboundary/LatticeCones.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Coboundary/Coboundary/LatticeCones.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoboundaryExpanders.Construction`, with `open scoped Polynomial BigOperators`, `open RationalLattices InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone`):
--
--   ```lean
--   theorem uniform_infinite_coset_positive (n : ℕ) (hn : 2 ≤ n) :
--       ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Q < p →
--         ∀ j : ℕ, 0 < j → j < n-1 →
--           (TypedCosetFaces.complex (uLocalGroup p n (by omega))).chainComplex.ExactAt j
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoboundaryExpanders.Construction.R`, `OAI.CoboundaryExpanders.Construction.U`, `OAI.CoboundaryExpanders.Construction.uLocalGroup`, `OAI.CoboundaryExpanders.InfiniteChains.k`, `OAI.CoboundaryExpanders.TypedCosetFaces.Vertex`, `OAI.CoboundaryExpanders.TypedCosetFaces.complex`, `OAI.CoboundaryExpanders.TypedCosetFaces.instDecidableEqVertex` and `OAI.CoboundaryExpanders.InfiniteChains.Complex.chainComplex` (definitions bundle `OAIQ3Cb000` of this split).
--
--   **Used by.** The proofs of `OAI.CoboundaryExpanders.main` and `OAI.CoboundaryExpanders.uniform_gamma_vanishing` of this split import it.
-- source:
--   OpenAI, Bounded-degree coboundary expanders in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 177; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Coboundary/Coboundary/LatticeCones.lean (declaration OAI.CoboundaryExpanders.Construction.uniform_infinite_coset_positive)

import Mathlib
import Definitions.Def_OAIQ3Cb000

section

attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.Construction
open RationalLattices InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable (p n : ℕ) [Fact p.Prime]

theorem uniform_infinite_coset_positive (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Q < p →
      ∀ j : ℕ, 0 < j → j < n-1 →
        (TypedCosetFaces.complex (uLocalGroup p n (by omega))).chainComplex.ExactAt j := by
  sorry
end CoboundaryExpanders.Construction

end

end OAI
end

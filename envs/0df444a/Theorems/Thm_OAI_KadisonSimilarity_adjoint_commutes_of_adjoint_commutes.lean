-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_adjoint_commutes_of_adjoint_commutes
-- name    : OAI.KadisonSimilarity.adjoint_commutes_of_adjoint_commutes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T17:17:02.820001+00:00
-- url     : https://prove2.me/theorems/2e42ae6a-1804-4c02-93b6-0449d5a443db
-- title:
--   OAI.KadisonSimilarity.adjoint_commutes_of_adjoint_commutes: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.adjoint_commutes_of_adjoint_commutes` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordLevelRepeatedOperators.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordLevelRepeatedOperators.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem adjoint_commutes_of_adjoint_commutes (Y Q : H →L[ℂ] H)
--       (h : Y.comp Q.adjoint = Q.adjoint.comp Y) : Y.adjoint.comp Q = Q.comp Y.adjoint
--   ```
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` and `OAI.KadisonSimilarity.embedded_actions_adjoint_repeated_word` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordLevelRepeatedOperators.lean (declaration OAI.KadisonSimilarity.adjoint_commutes_of_adjoint_commutes)

import Mathlib
import Definitions.Def_OAIQ075A004

section

attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
  {G : ℕ → Type*}
  [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)]
  [∀ n, CompleteSpace (G n)]
  {H : Type*}
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {A : ℕ → Type*}
  [∀ s, Fintype (A s)]
  [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

variable (Y : H →L[ℂ] H)

theorem adjoint_commutes_of_adjoint_commutes (Y Q : H →L[ℂ] H)
    (h : Y.comp Q.adjoint = Q.adjoint.comp Y) : Y.adjoint.comp Q = Q.comp Y.adjoint := by
  sorry

end KadisonSimilarity

end

end OAI
end

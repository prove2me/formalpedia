-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourcePairCreate_inner_s50
-- name    : OAI.Laughlin.Fock.sourcePairCreate_inner_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:45:21.48683+00:00
-- url     : https://prove2.me/theorems/839a5fb8-39f8-4608-8ffa-72dbd309a6d4
-- title:
--   OAI.Laughlin.Fock.sourcePairCreate_inner_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourcePairCreate_inner` of [lean/OAI/Analysis/Laughlin/Fock/NormalSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/NormalSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem sourcePairCreate_inner_s50 (Q : ℕ) (hQ : 2 ≤ Q)
--       (p q : Fin (2*Q-2+1)) (y z : Space Q) :
--       occupationInner Q (sourcePairCreateEnd Q p.val y) (sourcePairCreateEnd Q q.val z) =
--         (if p=q then (1 : ℂ) else 0) * occupationInner Q y z +
--         (∑ i, ∑ j, (complexThreeGram Q-1) (p,i) (q,j) *
--           occupationInner Q (annihilate i y) (annihilate j z)) +
--         occupationInner Q (sourcePairEnd Q q.val y) (sourcePairEnd Q p.val z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.Orbital` (definitions bundle `OAIQ050L003` of this split); `OAI.Laughlin.Fock.occupationInner` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.complexThreeGram` and `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ050L011` of this split); `OAI.Laughlin.Fock.sourcePairCreateEnd` and `OAI.Laughlin.Fock.sourcePairEnd` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space` and `OAI.Laughlin.Fock.annihilate` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/NormalSquare.lean (declaration OAI.Laughlin.Fock.sourcePairCreate_inner)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L011
import Definitions.Def_OAIQ050L012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem sourcePairCreate_inner_s50 (Q : ℕ) (hQ : 2 ≤ Q)
    (p q : Fin (2*Q-2+1)) (y z : Space Q) :
    occupationInner Q (sourcePairCreateEnd Q p.val y) (sourcePairCreateEnd Q q.val z) =
      (if p=q then (1 : ℂ) else 0) * occupationInner Q y z +
      (∑ i, ∑ j, (complexThreeGram Q-1) (p,i) (q,j) *
        occupationInner Q (annihilate i y) (annihilate j z)) +
      occupationInner Q (sourcePairEnd Q q.val y) (sourcePairEnd Q p.val z) := by
  sorry

end Laughlin.Fock

end OAI
end

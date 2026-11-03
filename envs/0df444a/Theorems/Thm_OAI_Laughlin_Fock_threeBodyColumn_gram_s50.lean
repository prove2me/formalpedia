-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_threeBodyColumn_gram_s50
-- name    : OAI.Laughlin.Fock.threeBodyColumn_gram_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:45:27.288682+00:00
-- url     : https://prove2.me/theorems/bfb2e98e-5d1c-432a-8a8c-5bdd84636f63
-- title:
--   OAI.Laughlin.Fock.threeBodyColumn_gram_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.threeBodyColumn_gram` of [lean/OAI/Analysis/Laughlin/ThreeBody/Gram.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/Gram.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem threeBodyColumn_gram_s50 (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2)
--       (i j : Fin (Q+1)) :
--       occupationInner Q (threeBodyColumn Q p i) (threeBodyColumn Q q j) =
--         (if p = q then (1 : ℂ) else 0)*(if i = j then (1 : ℂ) else 0) -
--         2 * ∑ t, (pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.pairCoefficient` and `OAI.Laughlin.Fock.occupationInner` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.threeBodyColumn` (definitions bundle `OAIQ050L012` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.threeWedge_zero_of_gram_zero_s50` and `OAI.Laughlin.Spin.normalizedCoupledDescendant_eigen_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/Gram.lean (declaration OAI.Laughlin.Fock.threeBodyColumn_gram)

import Mathlib
import Definitions.Def_OAIQ050L012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem threeBodyColumn_gram_s50 (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2)
    (i j : Fin (Q+1)) :
    occupationInner Q (threeBodyColumn Q p i) (threeBodyColumn Q q j) =
      (if p = q then (1 : ℂ) else 0)*(if i = j then (1 : ℂ) else 0) -
      2 * ∑ t, (pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ) := by
  sorry

end Laughlin.Fock

end OAI
end

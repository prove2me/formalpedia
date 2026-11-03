-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_threeBodyGram_highest_first_coordinate_s50
-- name    : OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:45:54.341126+00:00
-- url     : https://prove2.me/theorems/74325d8c-37f9-4772-a7ec-d6d2edd8ca9c
-- title:
--   OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate` of [lean/OAI/Analysis/Laughlin/ThreeBody/HighestReadout.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HighestReadout.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem threeBodyGram_highest_first_coordinate_s50 (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
--       (∑ q : Fin (z+1), threeBodyGramSlice Q z hz ⟨0,by omega⟩ q *
--         Spin.highestUnit (2*Q-2) Q z q.val) =
--         (1+gramEigenvalueFormula Q z)*Spin.highestUnit (2*Q-2) Q z 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.highestUnit` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.gramEigenvalueFormula` (definitions bundle `OAIQ050L008` of this split); `OAI.Laughlin.Fock.threeBodyGramSlice` (definitions bundle `OAIQ050L013` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Spin.normalizedCoupledDescendant_eigen_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HighestReadout.lean (declaration OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate)

import Mathlib
import Definitions.Def_OAIQ050L013

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem threeBodyGram_highest_first_coordinate_s50 (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (∑ q : Fin (z+1), threeBodyGramSlice Q z hz ⟨0,by omega⟩ q *
      Spin.highestUnit (2*Q-2) Q z q.val) =
      (1+gramEigenvalueFormula Q z)*Spin.highestUnit (2*Q-2) Q z 0 := by
  sorry

end Laughlin.Fock

end OAI
end

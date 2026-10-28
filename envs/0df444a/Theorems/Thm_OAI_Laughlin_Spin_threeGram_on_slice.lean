-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_threeGram_on_slice
-- name    : OAI.Laughlin.Spin.threeGram_on_slice
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:29:00.106286+00:00
-- url     : https://prove2.me/theorems/a9d0b584-4c91-4ce3-aa65-c74e099f0d20
-- title:
--   OAI.Laughlin.Spin.threeGram_on_slice: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.threeGram_on_slice` of [lean/OAI/Analysis/Laughlin/ThreeBody/HighestEigen.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HighestEigen.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem threeGram_on_slice (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (p q : Fin (z+1)) :
--       threeGram Q (weightSliceIndex (2*Q-2) Q z (by omega) hz p)
--         (weightSliceIndex (2*Q-2) Q z (by omega) hz q) = Fock.threeBodyGramSlice Q z hz p q
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.threeGram` and `OAI.Laughlin.Spin.weightSliceIndex` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Fock.threeBodyGramSlice` (definitions bundle `OAIQ047L001` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.complexThreeSpinProjector_eigen` and `OAI.Laughlin.Fock.physical_threeBody_budget_eventually` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HighestEigen.lean (declaration OAI.Laughlin.Spin.threeGram_on_slice)

import Mathlib
import Definitions.Def_OAIQ047L000
import Definitions.Def_OAIQ047L001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem threeGram_on_slice (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (p q : Fin (z+1)) :
    threeGram Q (weightSliceIndex (2*Q-2) Q z (by omega) hz p)
      (weightSliceIndex (2*Q-2) Q z (by omega) hz q) = Fock.threeBodyGramSlice Q z hz p q := by
  sorry

end Laughlin.Spin

end OAI
end

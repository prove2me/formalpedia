-- Prove2me | Theorems.Thm_OAI_Laughlin_normalizedPairState_lowering_s50
-- name    : OAI.Laughlin.normalizedPairState_lowering_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:49:36.164182+00:00
-- url     : https://prove2.me/theorems/ecba3d9a-33a4-4356-ae95-806c1e353b41
-- title:
--   OAI.Laughlin.normalizedPairState_lowering_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.normalizedPairState_lowering` of [lean/OAI/Analysis/Laughlin/Pair/NormalizedLadder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/NormalizedLadder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin`):
--
--   ```lean
--   theorem normalizedPairState_lowering_s50 (Q p i j : ℕ) (hQ : 0 < Q)
--       (hp : p < 2*Q-2) (hi : i ≤ Q) (hj : j ≤ Q) :
--       lowerPair Q (normalizedPairState Q p) i j =
--         Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*normalizedPairState Q (p+1) i j
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.lowerPair` (definitions bundle `OAIQ050L009` of this split); `OAI.Laughlin.normalizedPairState` (definitions bundle `OAIQ050L015` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Spin.pairCoefficient_tensor_lowering_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/NormalizedLadder.lean (declaration OAI.Laughlin.normalizedPairState_lowering)

import Mathlib
import Definitions.Def_OAIQ050L015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem normalizedPairState_lowering_s50 (Q p i j : ℕ) (hQ : 0 < Q)
    (hp : p < 2*Q-2) (hi : i ≤ Q) (hj : j ≤ Q) :
    lowerPair Q (normalizedPairState Q p) i j =
      Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*normalizedPairState Q (p+1) i j := by
  sorry

end Laughlin

end OAI
end

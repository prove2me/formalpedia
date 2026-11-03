-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_pairTensorLower_weight_s50
-- name    : OAI.Laughlin.Spin.pairTensorLower_weight_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:47:32.268121+00:00
-- url     : https://prove2.me/theorems/eda4af77-ec4c-4f2b-b225-53883c87f3ac
-- title:
--   OAI.Laughlin.Spin.pairTensorLower_weight_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.pairTensorLower_weight` of [lean/OAI/Analysis/Laughlin/Pair/TensorLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/TensorLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`):
--
--   ```lean
--   theorem pairTensorLower_weight_s50 (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
--       (x y : Fin (Q+1)) :
--       pairTensorLower Q p x y * Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
--         lowerPair Q (normalizedPairState Q p) x.val y.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.lowerPair` (definitions bundle `OAIQ050L009` of this split); `OAI.Laughlin.Spin.pairTensorLower` (definitions bundle `OAIQ050L014` of this split); `OAI.Laughlin.normalizedPairState` (definitions bundle `OAIQ050L015` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Rotation.physicalPairInclusion_SU2_s50`, `OAI.Laughlin.Spin.pairCoefficient_tensor_lowering_s50` and `OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/TensorLower.lean (declaration OAI.Laughlin.Spin.pairTensorLower_weight)

import Mathlib
import Definitions.Def_OAIQ050L014
import Definitions.Def_OAIQ050L015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem pairTensorLower_weight_s50 (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorLower Q p x y * Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      lowerPair Q (normalizedPairState Q p) x.val y.val := by
  sorry

end Laughlin.Spin

end OAI
end

-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_pairCoefficient_tensor_lowering_s50
-- name    : OAI.Laughlin.Spin.pairCoefficient_tensor_lowering_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:46:31.460441+00:00
-- url     : https://prove2.me/theorems/3947fc40-7128-4bb9-beb4-1cdfa13ec1a8
-- title:
--   OAI.Laughlin.Spin.pairCoefficient_tensor_lowering_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.pairCoefficient_tensor_lowering` of [lean/OAI/Analysis/Laughlin/Pair/TensorLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/TensorLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`):
--
--   ```lean
--   theorem pairCoefficient_tensor_lowering_s50 (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
--       (x y : Fin (Q+1)) :
--       pairTensorLower Q p x y = ladder (2*Q-2) p * pairCoefficient Q (p+1) x y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.ladder` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.pairCoefficient` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Spin.pairTensorLower` (definitions bundle `OAIQ050L014` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.fourPairEmbedding_contract_s50`, `OAI.Laughlin.Rotation.physicalPairInclusion_SU2_s50` and `OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/TensorLower.lean (declaration OAI.Laughlin.Spin.pairCoefficient_tensor_lowering)

import Mathlib
import Definitions.Def_OAIQ050L014

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem pairCoefficient_tensor_lowering_s50 (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorLower Q p x y = ladder (2*Q-2) p * pairCoefficient Q (p+1) x y := by
  sorry

end Laughlin.Spin

end OAI
end

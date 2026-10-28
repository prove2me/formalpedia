-- Prove2me | Theorems.Thm_OAI_DimensionTen_linear_composite_not_separable_s2
-- name    : OAI.DimensionTen.linear_composite_not_separable_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:31:22.356861+00:00
-- url     : https://prove2.me/theorems/6b0e80d2-db65-47af-bae4-8b0568d2e9cc
-- title:
--   OAI.DimensionTen.linear_composite_not_separable_s2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.linear_composite_not_separable` of [lean/OAI/Analysis/Quantum/DimensionTen/Channel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Channel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen`, with `open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder`, `open Matrix`):
--
--   ```lean
--   lemma linear_composite_not_separable_s2 :
--       ¬ ChannelCompletion.Separable
--         (ChannelCompletion.choi (phiTwoLinear.comp phiOneLinear))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ChannelCompletion.choi` (definitions bundle `OAIQ057D000` of this split); `OAI.DimensionTen.Mat` (definitions bundle `OAIQ057D003` of this split); `OAI.DimensionTen.phiOneLinear` (definitions bundle `OAIQ057D009` of this split); `OAI.DimensionTen.phiTwoLinear` (definitions bundle `OAIQ057D013` of this split); `OAI.ChannelCompletion.Mat` and `OAI.ChannelCompletion.Separable` (the published bundle `Def_DimensionTenChannel`).
--
--   **Used by.** The proof of `OAI.DimensionTen.main_channel_conditional_s2` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Channel.lean (declaration OAI.DimensionTen.linear_composite_not_separable)

import Mathlib
import Definitions.Def_DimensionTenChannel
import Definitions.Def_OAIQ057D013

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace DimensionTen

lemma linear_composite_not_separable_s2 :
    ¬ ChannelCompletion.Separable
      (ChannelCompletion.choi (phiTwoLinear.comp phiOneLinear)) := by
  sorry

end DimensionTen

end

end OAI
end

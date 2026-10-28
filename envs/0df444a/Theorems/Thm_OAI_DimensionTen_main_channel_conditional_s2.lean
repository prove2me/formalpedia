-- Prove2me | Theorems.Thm_OAI_DimensionTen_main_channel_conditional_s2
-- name    : OAI.DimensionTen.main_channel_conditional_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:42:02.157613+00:00
-- url     : https://prove2.me/theorems/9ce678c5-a300-4669-a556-2006712d50b7
-- title:
--   OAI.DimensionTen.main_channel_conditional_s2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.main_channel_conditional` of [lean/OAI/Analysis/Quantum/DimensionTen/Channel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Channel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen`, with `open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder`, `open Matrix`):
--
--   ```lean
--   theorem main_channel_conditional_s2 (hsr : PublishedChoi21) :
--       ChannelCompletion.PPT channel ∧ ChannelCompletion.TracePreserving channel ∧
--         ¬ ChannelCompletion.EntanglementBreaking (channel.comp channel)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ChannelCompletion.Space` (definitions bundle `OAIQ057D000` of this split); `OAI.DimensionTen.PublishedChoi21` and `OAI.DimensionTen.channel` (definitions bundle `OAIQ057D013` of this split); `OAI.ChannelCompletion.EntanglementBreaking`, `OAI.ChannelCompletion.Mat`, `OAI.ChannelCompletion.PPT` and `OAI.ChannelCompletion.TracePreserving` (the published bundle `Def_DimensionTenChannel`).
--
--   **Used by.** The proof of `OAI.DimensionTen.exists_channel_fin21` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Channel.lean (declaration OAI.DimensionTen.main_channel_conditional)

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

theorem main_channel_conditional_s2 (hsr : PublishedChoi21) :
    ChannelCompletion.PPT channel ∧ ChannelCompletion.TracePreserving channel ∧
      ¬ ChannelCompletion.EntanglementBreaking (channel.comp channel) := by
  sorry

end DimensionTen

end

end OAI
end

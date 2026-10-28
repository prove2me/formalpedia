-- Prove2me | Theorems.Thm_OAI_DimensionTen_Border_some_ten_minor_s2
-- name    : OAI.DimensionTen.Border.some_ten_minor_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:30:35.655596+00:00
-- url     : https://prove2.me/theorems/f18315b3-fc15-4a54-8269-acb5082eb884
-- title:
--   OAI.DimensionTen.Border.some_ten_minor_s2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.Border.some_ten_minor` of [lean/OAI/Analysis/Quantum/DimensionTen/EvaluationMinors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/EvaluationMinors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen.Border`, with `open Polynomial Matrix`):
--
--   ```lean
--   lemma some_ten_minor_s2 : ∃ a : Fin 10 → Fin 20, Function.Injective a ∧
--       (evaluationMatrix.submatrix firstTen a).det ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.Border.fQ` (definitions bundle `OAIQ057D000` of this split); `OAI.DimensionTen.Border.firstTen` (definitions bundle `OAIQ057D003` of this split); `OAI.DimensionTen.Border.K` (definitions bundle `OAIQ057D009` of this split); `OAI.DimensionTen.Border.evaluationMatrix` (definitions bundle `OAIQ057D011` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.veronese_family_general_position_s2` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/EvaluationMinors.lean (declaration OAI.DimensionTen.Border.some_ten_minor)

import Mathlib
import Definitions.Def_OAIQ057D011

section

attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

lemma some_ten_minor_s2 : ∃ a : Fin 10 → Fin 20, Function.Injective a ∧
    (evaluationMatrix.submatrix firstTen a).det ≠ 0 := by
  sorry

end DimensionTen.Border

end
end

end OAI
end

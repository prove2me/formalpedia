-- Prove2me | Theorems.Thm_OAI_DimensionTen_Border_minors_embedding_s2
-- name    : OAI.DimensionTen.Border.minors_embedding_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:31:33.891708+00:00
-- url     : https://prove2.me/theorems/33966c96-6d5a-4ed2-bc31-cf8b703f70fd
-- title:
--   OAI.DimensionTen.Border.minors_embedding_s2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.Border.minors_embedding` of [lean/OAI/Analysis/Quantum/DimensionTen/AlphaMinors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/AlphaMinors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen.Border`, with `open Matrix`):
--
--   ```lean
--   lemma minors_embedding_s2 {R : Type*} [Field R] [Algebra ℚ R] (σ : L →ₐ[ℚ] R) :
--       minor (Fin.cons 1 (fun j => σ (alpha j))) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.Border.L` and `OAI.DimensionTen.Border.fQ` (definitions bundle `OAIQ057D000` of this split); `OAI.DimensionTen.Border.minor` (definitions bundle `OAIQ057D009` of this split); `OAI.DimensionTen.Border.alpha` and `OAI.DimensionTen.Border.instFactIrreduciblePolynomialRatFQ` (definitions bundle `OAIQ057D011` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.Border.rank_points_s2` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/AlphaMinors.lean (declaration OAI.DimensionTen.Border.minors_embedding)

import Mathlib
import Definitions.Def_OAIQ057D011

section

attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma minors_embedding_s2 {R : Type*} [Field R] [Algebra ℚ R] (σ : L →ₐ[ℚ] R) :
    minor (Fin.cons 1 (fun j => σ (alpha j))) = 0 := by
  sorry

end DimensionTen.Border

end
end

end OAI
end

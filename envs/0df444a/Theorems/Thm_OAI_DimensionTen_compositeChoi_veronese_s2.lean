-- Prove2me | Theorems.Thm_OAI_DimensionTen_compositeChoi_veronese_s2
-- name    : OAI.DimensionTen.compositeChoi_veronese_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:30:41.579811+00:00
-- url     : https://prove2.me/theorems/fcbb2f5b-7bff-4990-8a4d-7e94b710094e
-- title:
--   OAI.DimensionTen.compositeChoi_veronese_s2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.compositeChoi_veronese` of [lean/OAI/Analysis/Quantum/DimensionTen/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen`, with `open scoped Matrix Kronecker ComplexOrder`, `open Matrix`):
--
--   ```lean
--   lemma compositeChoi_veronese_s2 (x : Fin 4 → ℂ) :
--       star (productVector (veronese x) (veronese x)) ⬝ᵥ
--         (compositeChoi *ᵥ productVector (veronese x) (veronese x)) =
--         6 * (pencilMap (pure x)).det
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.productVector` and `OAI.DimensionTen.pure` (definitions bundle `OAIQ057D007` of this split); `OAI.DimensionTen.pencilMap` (definitions bundle `OAIQ057D009` of this split); `OAI.DimensionTen.veronese` (definitions bundle `OAIQ057D010` of this split); `OAI.DimensionTen.compositeChoi` (definitions bundle `OAIQ057D011` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.linear_composite_not_separable_s2` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Main.lean (declaration OAI.DimensionTen.compositeChoi_veronese)

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
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma compositeChoi_veronese_s2 (x : Fin 4 → ℂ) :
    star (productVector (veronese x) (veronese x)) ⬝ᵥ
      (compositeChoi *ᵥ productVector (veronese x) (veronese x)) =
      6 * (pencilMap (pure x)).det := by
  sorry

end DimensionTen

end
end

end OAI
end

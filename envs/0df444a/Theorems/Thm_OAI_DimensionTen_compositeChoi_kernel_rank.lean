-- Prove2me | Theorems.Thm_OAI_DimensionTen_compositeChoi_kernel_rank
-- name    : OAI.DimensionTen.compositeChoi_kernel_rank
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T01:51:55.98514+00:00
-- url     : https://prove2.me/theorems/c47913ee-65e7-4e88-abed-7f70945b95b0
-- title:
--   OAI.DimensionTen.compositeChoi_kernel_rank: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.compositeChoi_kernel_rank` of [lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen`, with `open scoped Matrix Kronecker ComplexOrder`, `open Matrix`):
--
--   ```lean
--   lemma compositeChoi_kernel_rank {x : Fin 4 → ℂ} (hx : (pencil x).rank < 4) :
--       compositeChoi *ᵥ productVector (veronese x) (veronese x) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.pencil` and `OAI.DimensionTen.veronese` (definitions bundle `OAIQ033D009` of this split); `OAI.DimensionTen.compositeChoi` and `OAI.DimensionTen.productVector` (the published bundle `Def_DimensionTenPair`).
--
--   **Used by.** The proof of `OAI.DimensionTen.main_pair` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Main.lean (declaration OAI.DimensionTen.compositeChoi_kernel_rank)

import Mathlib
import Definitions.Def_DimensionTenPair
import Definitions.Def_OAIQ033D009

section

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

lemma compositeChoi_kernel_rank {x : Fin 4 → ℂ} (hx : (pencil x).rank < 4) :
    compositeChoi *ᵥ productVector (veronese x) (veronese x) = 0 := by
  sorry

end DimensionTen

end
end

end OAI
end

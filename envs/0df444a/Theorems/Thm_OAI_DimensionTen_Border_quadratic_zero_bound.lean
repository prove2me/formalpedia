-- Prove2me | Theorems.Thm_OAI_DimensionTen_Border_quadratic_zero_bound
-- name    : OAI.DimensionTen.Border.quadratic_zero_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T02:38:48.032342+00:00
-- url     : https://prove2.me/theorems/7affa58a-654e-4e9d-ab18-e08e1415f92e
-- title:
--   OAI.DimensionTen.Border.quadratic_zero_bound: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.Border.quadratic_zero_bound` of [lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/QuadraticBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/QuadraticBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen.Border`, with `open Matrix`):
--
--   ```lean
--   lemma quadratic_zero_bound (q : QuadraticIndex → ℂ) (hq : q ≠ 0) :
--       (Finset.univ.filter (fun k : Fin 20 => quadraticEval q (chart (points k)) = 0)).card ≤ 9
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.QuadraticIndex` (definitions bundle `OAIQ033D002` of this split); `OAI.DimensionTen.chart` (definitions bundle `OAIQ033D009` of this split); `OAI.DimensionTen.quadraticEval` (definitions bundle `OAIQ033D013` of this split); `OAI.DimensionTen.Border.points` (definitions bundle `OAIQ033D014` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.main_pair` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/QuadraticBounds.lean (declaration OAI.DimensionTen.Border.quadratic_zero_bound)

import Mathlib
import Definitions.Def_OAIQ033D009
import Definitions.Def_OAIQ033D014

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma quadratic_zero_bound (q : QuadraticIndex → ℂ) (hq : q ≠ 0) :
    (Finset.univ.filter (fun k : Fin 20 => quadraticEval q (chart (points k)) = 0)).card ≤ 9 := by
  sorry

end DimensionTen.Border

end
end

end OAI
end

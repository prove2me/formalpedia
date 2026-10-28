-- Prove2me | Theorems.Thm_OAI_DimensionTen_Mod131_iterate13_s2
-- name    : OAI.DimensionTen.Mod131.iterate13_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:03:24.720832+00:00
-- url     : https://prove2.me/theorems/3abb0696-ef4b-4a3e-ab19-c9e14a856d08
-- title:
--   OAI.DimensionTen.Mod131.iterate13_s2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.Mod131.iterate13` of [lean/OAI/Analysis/Quantum/DimensionTen/Mod131Powers07.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod131Powers07.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen.Mod131`, with `open Polynomial`):
--
--   ```lean
--   theorem iterate13_s2 {R : Type*} [CommRing R] [CharP R 131]
--       (z : R) (hz : f z = 0) : z ^ (131 ^ 13) = u13 z
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.Mod131.f` (definitions bundle `OAIQ057D003` of this split); `OAI.DimensionTen.Mod131.u13` (definitions bundle `OAIQ057D009` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.fixed_mod131_s2` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod131Powers07.lean (declaration OAI.DimensionTen.Mod131.iterate13)

import Mathlib
import Definitions.Def_OAIQ057D009

section

attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem iterate13_s2 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 13) = u13 z := by
  sorry

end DimensionTen.Mod131

end

end OAI
end

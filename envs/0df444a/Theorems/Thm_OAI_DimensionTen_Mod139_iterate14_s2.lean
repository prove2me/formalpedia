-- Prove2me | Theorems.Thm_OAI_DimensionTen_Mod139_iterate14_s2
-- name    : OAI.DimensionTen.Mod139.iterate14_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:28:40.582427+00:00
-- url     : https://prove2.me/theorems/c74af4b7-ad6c-406d-a4cf-7329dde5c3ef
-- title:
--   OAI.DimensionTen.Mod139.iterate14_s2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.Mod139.iterate14` of [lean/OAI/Analysis/Quantum/DimensionTen/Mod139Powers07.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Powers07.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen.Mod139`, with `open Polynomial`):
--
--   ```lean
--   theorem iterate14_s2 {R : Type*} [CommRing R] [CharP R 139]
--       (z : R) (hz : f z = 0) : z ^ (139 ^ 14) = u14 z
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.Mod139.f` (definitions bundle `OAIQ057D005` of this split); `OAI.DimensionTen.Mod139.u14` (definitions bundle `OAIQ057D009` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.pow_mod139_s2` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Powers07.lean (declaration OAI.DimensionTen.Mod139.iterate14)

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
namespace DimensionTen.Mod139

theorem iterate14_s2 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 14) = u14 z := by
  sorry

end DimensionTen.Mod139

end

end OAI
end

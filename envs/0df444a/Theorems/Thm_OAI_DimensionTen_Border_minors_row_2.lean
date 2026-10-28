-- Prove2me | Theorems.Thm_OAI_DimensionTen_Border_minors_row_2
-- name    : OAI.DimensionTen.Border.minors_row_2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T02:05:13.137389+00:00
-- url     : https://prove2.me/theorems/96e1a555-6899-4133-8ec2-9cd7678d10dc
-- title:
--   OAI.DimensionTen.Border.minors_row_2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.Border.minors_row_2` of [lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/MinorData.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/MinorData.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen.Border`, with `open Matrix`):
--
--   ```lean
--   lemma minors_row_2 {R : Type*} [CommRing R] (x : Fin 4 → R) :
--       minor x 2 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
--         (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.Border.D` (definitions bundle `OAIQ033D000` of this split); `OAI.DimensionTen.Border.high` and `OAI.DimensionTen.Border.homogeneousLow` (definitions bundle `OAIQ033D003` of this split); `OAI.DimensionTen.Border.H` and `OAI.DimensionTen.Border.minor` (definitions bundle `OAIQ033D012` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.Border.minors_eq` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/MinorData.lean (declaration OAI.DimensionTen.Border.minors_row_2)

import Mathlib
import Definitions.Def_OAIQ033D012

section

attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma minors_row_2 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 2 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 2 := by
  sorry

end DimensionTen.Border

end
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_DimensionTen_fixed_mod139_s2
-- name    : OAI.DimensionTen.fixed_mod139_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:46:22.702161+00:00
-- url     : https://prove2.me/theorems/97b5163f-0b06-4112-943c-14b9cdfa1d28
-- title:
--   OAI.DimensionTen.fixed_mod139_s2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.fixed_mod139` of [lean/OAI/Analysis/Quantum/DimensionTen/ModularPermutations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/ModularPermutations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen`, with `open Polynomial`):
--
--   ```lean
--   lemma fixed_mod139_s2 {k ι : Type*} [Field k] [CharP k 139] [Fintype ι] [DecidableEq ι]
--       (r : ι → k) (hinj : Function.Injective r) (π : Equiv.Perm ι)
--       (hfact : Mod139.f X = ∏ i, (X - C (r i)))
--       (hfrob : ∀ i, r (π i) = r i ^ 139) :
--       Fintype.card {i : ι // (π ^ 1) i = i} = 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.Mod139.f` (definitions bundle `OAIQ057D005` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.root_action_full_symmetric_s2` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/ModularPermutations.lean (declaration OAI.DimensionTen.fixed_mod139)

import Mathlib
import Definitions.Def_OAIQ057D005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial
namespace DimensionTen

lemma fixed_mod139_s2 {k ι : Type*} [Field k] [CharP k 139] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hinj : Function.Injective r) (π : Equiv.Perm ι)
    (hfact : Mod139.f X = ∏ i, (X - C (r i)))
    (hfrob : ∀ i, r (π i) = r i ^ 139) :
    Fintype.card {i : ι // (π ^ 1) i = i} = 1 := by
  sorry

end DimensionTen

end
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_DimensionTen_exists_swap_of_mod131
-- name    : OAI.DimensionTen.exists_swap_of_mod131
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T01:52:43.164111+00:00
-- url     : https://prove2.me/theorems/3e8d1f95-2695-4806-9af3-f148d5802151
-- title:
--   OAI.DimensionTen.exists_swap_of_mod131: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.exists_swap_of_mod131` of [lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/GaloisCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/GaloisCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen`, with `open NumberField Polynomial`):
--
--   ```lean
--   lemma exists_swap_of_mod131
--       (h131 : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X) :
--       ∃ σ : Gal(K/ℚ), (MulAction.toPerm (σ ^ 17) : Equiv.Perm (f.rootSet K)).IsSwap
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.Mod131.f` (definitions bundle `OAIQ033D003` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.Border.quadratic_zero_bound` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/GaloisCertificate.lean (declaration OAI.DimensionTen.exists_swap_of_mod131)

import Mathlib
import Definitions.Def_OAIQ033D003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

section Roots
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [DecidableEq K]
variable (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hp : (f.map (algebraMap ℤ K)).Splits)
    (hc : Fintype.card (f.rootSet K) = 20)

include hm hs hp hc in
lemma exists_swap_of_mod131
    (h131 : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X) :
    ∃ σ : Gal(K/ℚ), (MulAction.toPerm (σ ^ 17) : Equiv.Perm (f.rootSet K)).IsSwap := by
  sorry

end Roots
end DimensionTen

end
end

end OAI
end

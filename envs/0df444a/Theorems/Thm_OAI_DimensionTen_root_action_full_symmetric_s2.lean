-- Prove2me | Theorems.Thm_OAI_DimensionTen_root_action_full_symmetric_s2
-- name    : OAI.DimensionTen.root_action_full_symmetric_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:47:57.184767+00:00
-- url     : https://prove2.me/theorems/ff3a2554-69e5-45ec-8ff7-ad04ce439d00
-- title:
--   OAI.DimensionTen.root_action_full_symmetric_s2: intermediate lemma from OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DimensionTen.root_action_full_symmetric` of [lean/OAI/Analysis/Quantum/DimensionTen/GaloisCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/GaloisCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DimensionTen`, with `open NumberField Polynomial`):
--
--   ```lean
--   lemma root_action_full_symmetric_s2
--       (h41 : f.map (Int.castRingHom (ZMod 41)) = Mod41.f X)
--       (h131 : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X)
--       (h139 : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
--       Function.Surjective (MulAction.toPermHom Gal(K/ℚ) (f.rootSet K))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions` (definitions bundle `OAIQ057D000` of this split); `OAI.DimensionTen.Mod41.f` (definitions bundle `OAIQ057D001` of this split); `OAI.DimensionTen.Mod131.f` (definitions bundle `OAIQ057D003` of this split); `OAI.DimensionTen.Mod139.f` (definitions bundle `OAIQ057D005` of this split).
--
--   **Used by.** The proof of `OAI.DimensionTen.veronese_family_general_position_s2` of this split imports it.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/GaloisCertificate.lean (declaration OAI.DimensionTen.root_action_full_symmetric)

import Mathlib
import Definitions.Def_OAIQ057D000
import Definitions.Def_OAIQ057D001
import Definitions.Def_OAIQ057D003
import Definitions.Def_OAIQ057D005

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
lemma root_action_full_symmetric_s2
    (h41 : f.map (Int.castRingHom (ZMod 41)) = Mod41.f X)
    (h131 : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X)
    (h139 : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    Function.Surjective (MulAction.toPermHom Gal(K/ℚ) (f.rootSet K)) := by
  sorry

end Roots
end DimensionTen

end
end

end OAI
end

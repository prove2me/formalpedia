-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_gns_vectorState
-- name    : OAI.Kadison.FreeBlocks.gns_vectorState
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:34:13.846572+00:00
-- url     : https://prove2.me/theorems/ea5e1545-6116-4a19-bdcc-bf5de47b2765
-- title:
--   OAI.Kadison.FreeBlocks.gns_vectorState: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator`, `open UniformSpace`):
--
--   ```lean
--   lemma gns_vectorState (τ : A →ₚ[ℂ] ℂ) (a : A) :
--       CornerSymmetrization.vectorState (TracialGNS.vacuum τ) (τ.gnsStarAlgHom a)=τ a
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.vacuum` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.CornerSymmetrization.vectorState` (definitions bundle `OAIQ039C004` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.normal_free_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open UniformSpace

namespace Kadison.FreeBlocks

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma gns_vectorState (τ : A →ₚ[ℂ] ℂ) (a : A) :
    CornerSymmetrization.vectorState (TracialGNS.vacuum τ) (τ.gnsStarAlgHom a)=τ a := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end

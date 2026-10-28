-- Prove2me | Theorems.Thm_OAI_Kadison_VectorGNS_factorTrace_inclusion_normal
-- name    : OAI.Kadison.VectorGNS.factorTrace_inclusion_normal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:59:09.113461+00:00
-- url     : https://prove2.me/theorems/5f9de75e-fa7b-4cc9-b7da-8fb8bc5012f8
-- title:
--   OAI.Kadison.VectorGNS.factorTrace_inclusion_normal: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.VectorGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open FreeWordTensor FreeWordAction FreeBlocks`):
--
--   ```lean
--   lemma factorTrace_inclusion_normal (D : VonNeumannAlgebra H)
--       (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
--       NormalGNS.BoundedWOTContinuous D
--         (factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
--           (inclusion_injective M D hDM))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.VectorGNS.subalgebraTrace` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.FreeBlocks.factorTrace` (definitions bundle `OAIQ039C046` of this split); `OAI.Kadison.VectorGNS.inclusion` (definitions bundle `OAIQ039C060` of this split); `OAI.Kadison.VectorGNS.vectorState` (definitions bundle `OAIQ039C065` of this split); `OAI.Kadison.VectorGNS.inclusion_injective` (definitions bundle `OAIQ039C070` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.VectorGNS.free_original_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C065
import Definitions.Def_OAIQ039C070

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.VectorGNS

open FreeWordTensor FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

lemma factorTrace_inclusion_normal (D : VonNeumannAlgebra H)
    (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
    NormalGNS.BoundedWOTContinuous D
      (factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
        (inclusion_injective M D hDM)) := by
  sorry

end Kadison.VectorGNS

end

end
end

end OAI
end

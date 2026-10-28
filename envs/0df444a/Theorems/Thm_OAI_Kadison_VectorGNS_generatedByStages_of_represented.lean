-- Prove2me | Theorems.Thm_OAI_Kadison_VectorGNS_generatedByStages_of_represented
-- name    : OAI.Kadison.VectorGNS.generatedByStages_of_represented
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:47:44.220874+00:00
-- url     : https://prove2.me/theorems/475072c0-e20a-489b-86ca-3b9e827b7963
-- title:
--   OAI.Kadison.VectorGNS.generatedByStages_of_represented: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.VectorGNS`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`, `open FreeWordTensor FreeBlocks`):
--
--   ```lean
--   lemma generatedByStages_of_represented
--       (hgen : ∀ a : D,(a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
--         (NormalGNS.representedStages D I φ : Set (H →L[ℂ] H)))) :
--       GeneratedByStages D ξ I φ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.NormalGNS.representedStages` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.VectorGNS.GeneratedByStages` (definitions bundle `OAIQ039C064` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C061
import Definitions.Def_OAIQ039C064

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

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.VectorGNS

open FreeWordTensor FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (D : VonNeumannAlgebra H) (ξ : H)
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

lemma generatedByStages_of_represented
    (hgen : ∀ a : D,(a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (NormalGNS.representedStages D I φ : Set (H →L[ℂ] H)))) :
    GeneratedByStages D ξ I φ := by
  sorry

end Kadison.VectorGNS

end

end
end

end OAI
end

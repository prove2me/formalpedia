-- Prove2me | Theorems.Thm_OAI_Kadison_NormalGNS_matrix_stages_gns
-- name    : OAI.Kadison.NormalGNS.matrix_stages_gns
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:41:12.293178+00:00
-- url     : https://prove2.me/theorems/b18dfb10-2c4c-4ae1-9617-2f6efe813365
-- title:
--   OAI.Kadison.NormalGNS.matrix_stages_gns: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalGNS`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   theorem matrix_stages_gns (a : M)
--       (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
--         (representedStages M I φ : Set (H →L[ℂ] H)))) :
--       τ.gnsStarAlgHom a∈Set.centralizer (Set.centralizer
--         (TracialGNS.stageAlgebra τ I φ : Set _))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.TracialGNS.stageAlgebra` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.NormalGNS.representedStages` (definitions bundle `OAIQ039C061` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.VectorGNS.generatedByStages_of_represented` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C061

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
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

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] M)

include hnormal in
theorem matrix_stages_gns (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (representedStages M I φ : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈Set.centralizer (Set.centralizer
      (TracialGNS.stageAlgebra τ I φ : Set _)) := by
  sorry

end Kadison.NormalGNS

end

end
end

end OAI
end

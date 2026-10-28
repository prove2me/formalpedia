-- Prove2me | Theorems.Thm_OAI_Kadison_GeneratedMatrixBicommutant_in_represented
-- name    : OAI.Kadison.GeneratedMatrixBicommutant.in_represented
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:39:13.420475+00:00
-- url     : https://prove2.me/theorems/1c167bd0-3770-495e-9885-1ce690300779
-- title:
--   OAI.Kadison.GeneratedMatrixBicommutant.in_represented: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.GeneratedMatrixBicommutant`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma in_represented (a : algebra size stage φ) :
--       (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
--         (NormalGNS.representedStages (algebra size stage φ) (fun n => Fin (size n+1))
--           (stageHom size stage φ) : Set (H →L[ℂ] H)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.GeneratedMatrixBicommutant.algebra` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.GeneratedMatrixBicommutant.stageHom` (definitions bundle `OAIQ039C060` of this split); `OAI.Kadison.NormalGNS.representedStages` (definitions bundle `OAIQ039C061` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C060
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

namespace Kadison.GeneratedMatrixBicommutant

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] A)

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma in_represented (a : algebra size stage φ) :
    (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (NormalGNS.representedStages (algebra size stage φ) (fun n => Fin (size n+1))
        (stageHom size stage φ) : Set (H →L[ℂ] H))) := by
  sorry

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_Kadison_exists_separable_cstar_bicommutant
-- name    : OAI.Kadison.exists_separable_cstar_bicommutant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:39:43.72131+00:00
-- url     : https://prove2.me/theorems/ab19058a-d2cf-402d-8cf0-30499fe89b0b
-- title:
--   OAI.Kadison.exists_separable_cstar_bicommutant: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped Topology`):
--
--   ```lean
--   theorem exists_separable_cstar_bicommutant
--       {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
--       [TopologicalSpace.SeparableSpace H] (P : VonNeumannAlgebra H) :
--       ∃ S : StarSubalgebra ℂ (H →L[ℂ] H),IsClosed (S:Set (H →L[ℂ] H)) ∧
--         TopologicalSpace.SeparableSpace S ∧ S≤P.toStarSubalgebra ∧ NormalGNS.bicommutant S=P
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.bicommutant` (definitions bundle `OAIQ039C011` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.Decomposable.uniform_commutator_in_central_spectral_model_nonzero` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison

theorem exists_separable_cstar_bicommutant
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P : VonNeumannAlgebra H) :
    ∃ S : StarSubalgebra ℂ (H →L[ℂ] H),IsClosed (S:Set (H →L[ℂ] H)) ∧
      TopologicalSpace.SeparableSpace S ∧ S≤P.toStarSubalgebra ∧ NormalGNS.bicommutant S=P := by
  sorry

end Kadison

end

end
end

end OAI
end

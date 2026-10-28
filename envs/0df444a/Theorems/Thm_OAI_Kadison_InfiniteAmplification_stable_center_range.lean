-- Prove2me | Theorems.Thm_OAI_Kadison_InfiniteAmplification_stable_center_range
-- name    : OAI.Kadison.InfiniteAmplification.stable_center_range
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:44:01.401991+00:00
-- url     : https://prove2.me/theorems/d8eb4b3e-0352-46f5-b6b2-7e2fdab7848b
-- title:
--   OAI.Kadison.InfiniteAmplification.stable_center_range: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.InfiniteAmplification`):
--
--   ```lean
--   lemma stable_center_range (M : VonNeumannAlgebra H) (U : Space ℕ H ≃ₗᵢ[ℂ] K)
--       (Z : K →L[ℂ] K) (hZ : Z∈CentralCorner.center (UnitaryTransport.algebra U (algebra M))) :
--       ∃ a : CentralCorner.center M,U.conjStarAlgEquiv (map a.val)=Z
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CentralCorner.center` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.InfiniteAmplification.Space` and `OAI.Kadison.InfiniteAmplification.map` (definitions bundle `OAIQ039C006` of this split); `OAI.Kadison.InfiniteAmplification.algebra` (definitions bundle `OAIQ039C027` of this split); `OAI.Kadison.UnitaryTransport.algebra` (definitions bundle `OAIQ039C031` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CentralSpectral.stable_model_center` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C027
import Definitions.Def_OAIQ039C031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.InfiniteAmplification

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma stable_center_range (M : VonNeumannAlgebra H) (U : Space ℕ H ≃ₗᵢ[ℂ] K)
    (Z : K →L[ℂ] K) (hZ : Z∈CentralCorner.center (UnitaryTransport.algebra U (algebra M))) :
    ∃ a : CentralCorner.center M,U.conjStarAlgEquiv (map a.val)=Z := by
  sorry

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

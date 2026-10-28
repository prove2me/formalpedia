-- Prove2me | Theorems.Thm_OAI_HyperbolicObstruction_IncidenceTemplate_exists_finite_aspherical_hyperbolic_noAction
-- name    : OAI.HyperbolicObstruction.IncidenceTemplate.exists_finite_aspherical_hyperbolic_noAction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T05:31:30.329+00:00
-- url     : https://prove2.me/theorems/fa4a3ecb-8eb9-42bd-9ef3-426a05909e4a
-- title:
--   OAI.HyperbolicObstruction.IncidenceTemplate.exists_finite_aspherical_hyperbolic_noAction: intermediate lemma from OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HyperbolicObstruction.IncidenceTemplate.exists_finite_aspherical_hyperbolic_noAction` of [lean/OAI/Geometry/HyperbolicGroups/HyperbolicGroups/IndexedFillingValue.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/HyperbolicGroups/HyperbolicGroups/IndexedFillingValue.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HyperbolicObstruction.IncidenceTemplate`):
--
--   ```lean
--   theorem exists_finite_aspherical_hyperbolic_noAction :
--       ∃ K : FiniteComplex, ∃ x : K.Carrier, ∃ C : ℝ,
--       ConnectedSpace K.Carrier ∧ K.Aspherical x ∧ Infinite (FundamentalGroup K.Carrier x) ∧
--         0 ≤ C ∧ K.LinearDiskFilling C ∧
--         NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x) ∧
--         WordHyperbolic (FundamentalGroup K.Carrier x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HyperbolicObstruction.FiniteComplex`, `OAI.HyperbolicObstruction.NoGeometricCATZeroAction`, `OAI.HyperbolicObstruction.WordHyperbolic`, `OAI.HyperbolicObstruction.FiniteComplex.Aspherical`, `OAI.HyperbolicObstruction.FiniteComplex.Carrier`, `OAI.HyperbolicObstruction.FiniteComplex.LinearDiskFilling` and `OAI.HyperbolicObstruction.FiniteComplex.instTopologicalSpaceCarrier` (the published bundle `Def_HyperbolicObstruction`).
--
--   **Used by.** The proof of `OAI.HyperbolicObstruction.main` of this split imports it.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/HyperbolicGroups/HyperbolicGroups/IndexedFillingValue.lean (declaration OAI.HyperbolicObstruction.IncidenceTemplate.exists_finite_aspherical_hyperbolic_noAction)

import Mathlib
import Definitions.Def_HyperbolicObstruction

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction

namespace IncidenceTemplate
universe u

theorem exists_finite_aspherical_hyperbolic_noAction :
    ∃ K : FiniteComplex, ∃ x : K.Carrier, ∃ C : ℝ,
    ConnectedSpace K.Carrier ∧ K.Aspherical x ∧ Infinite (FundamentalGroup K.Carrier x) ∧
      0 ≤ C ∧ K.LinearDiskFilling C ∧
      NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x) ∧
      WordHyperbolic (FundamentalGroup K.Carrier x) := by
  sorry

end IncidenceTemplate

open Set Metric

end HyperbolicObstruction

end

end OAI
end

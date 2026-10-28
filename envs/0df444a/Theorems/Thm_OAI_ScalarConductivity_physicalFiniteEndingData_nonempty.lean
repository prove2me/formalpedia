-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_physicalFiniteEndingData_nonempty
-- name    : OAI.ScalarConductivity.physicalFiniteEndingData_nonempty
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:46:01.939747+00:00
-- url     : https://prove2.me/theorems/e3b3e9f2-1828-444c-ab35-98e48483df3e
-- title:
--   OAI.ScalarConductivity.physicalFiniteEndingData_nonempty: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.physicalFiniteEndingData_nonempty` of [lean/OAI/Analysis/Conductivity/Branching/PhysicalFiniteEndingData.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Branching/PhysicalFiniteEndingData.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set Filter Topology MeasureTheory Matrix UnitAddTorus`):
--
--   ```lean
--   lemma physicalFiniteEndingData_nonempty {s : Fin 3 → ℝ}
--       (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
--       (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h) :
--       Nonempty (PhysicalFiniteEndingData s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.torusQuadratic` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.PhysicalFiniteEndingData` (definitions bundle `OAIQ059C003` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.boundedRootSources_nonempty` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Branching/PhysicalFiniteEndingData.lean (declaration OAI.ScalarConductivity.physicalFiniteEndingData_nonempty)

import Mathlib
import Definitions.Def_OAIQ059C003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma physicalFiniteEndingData_nonempty {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h) :
    Nonempty (PhysicalFiniteEndingData s) := by
  sorry

end ScalarConductivity

end

end OAI
end

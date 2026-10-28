-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_expectedPressure_lower_smooth
-- name    : OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:09:28.372425+00:00
-- url     : https://prove2.me/theorems/afc608ca-9b30-4bf6-a41c-6ee9183612d7
-- title:
--   OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth` of [lean/OAI/Probability/Perceptron/Cavity/CavitySmoothLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavitySmoothLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma expectedPressure_lower_smooth (P : Measure BrownianPath) [IsProbabilityMeasure P]
--       (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
--       (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
--       (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {ε : ℝ} (hε : 0<ε) :
--       ∀ᶠ n : ℕ in atTop,(terminalVariational P α g.f).toReal-ε≤expectedPressure α 1 g.f (n+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.Jet3` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.terminalVariational` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.BrownianPath`, `OAI.SphericalPerceptronFreeEnergy.brownianEval`, `OAI.SphericalPerceptronFreeEnergy.expectedPressure` and `OAI.SphericalPerceptronFreeEnergy.instMeasurableSpaceBrownianPath` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.main` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavitySmoothLimit.lean (declaration OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma expectedPressure_lower_smooth (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,(terminalVariational P α g.f).toReal-ε≤expectedPressure α 1 g.f (n+1) := by
  sorry

end SphericalPerceptronFreeEnergy

end

end OAI
end

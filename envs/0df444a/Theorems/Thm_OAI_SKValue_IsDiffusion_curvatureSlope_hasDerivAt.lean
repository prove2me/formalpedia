-- Prove2me | Theorems.Thm_OAI_SKValue_IsDiffusion_curvatureSlope_hasDerivAt
-- name    : OAI.SKValue.IsDiffusion.curvatureSlope_hasDerivAt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:46:44.052781+00:00
-- url     : https://prove2.me/theorems/d9d57e86-a0b0-4be2-a2ce-8f811361cfc4
-- title:
--   OAI.SKValue.IsDiffusion.curvatureSlope_hasDerivAt: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.IsDiffusion.curvatureSlope_hasDerivAt` of [lean/OAI/Probability/SKValue/SKValue/Coercivity/CurvatureMoment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Coercivity/CurvatureMoment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   lemma IsDiffusion.curvatureSlope_hasDerivAt {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
--       (hX:IsDiffusion W γ X) {t c:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hc:ContinuousAt γ.coeff t) (he:γ.coeff t=c):
--       HasDerivAt (jetMoment W γ X (JetExpr.curvatureSlope c))
--         (∫ z,(iteratedDeriv 3 (deriv (phi W γ t)) (X t z))^2-
--           12*γ.coeff t*iteratedDeriv 1 (deriv (phi W γ t)) (X t z)*(iteratedDeriv 2 (deriv (phi W γ t)) (X t z))^2+
--           6*(γ.coeff t)^2*(iteratedDeriv 1 (deriv (phi W γ t)) (X t z))^4 ∂W.μ) t
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.jetMoment` and `OAI.SKValue.JetExpr.curvatureSlope` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.IsDiffusion`, `OAI.SKValue.OrderParameter` and `OAI.SKValue.phi` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.IsMinimizer.gradient_moment_contact` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Coercivity/CurvatureMoment.lean (declaration OAI.SKValue.IsDiffusion.curvatureSlope_hasDerivAt)

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000

section

attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma IsDiffusion.curvatureSlope_hasDerivAt {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t c:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hc:ContinuousAt γ.coeff t) (he:γ.coeff t=c):
    HasDerivAt (jetMoment W γ X (JetExpr.curvatureSlope c))
      (∫ z,(iteratedDeriv 3 (deriv (phi W γ t)) (X t z))^2-
        12*γ.coeff t*iteratedDeriv 1 (deriv (phi W γ t)) (X t z)*(iteratedDeriv 2 (deriv (phi W γ t)) (X t z))^2+
        6*(γ.coeff t)^2*(iteratedDeriv 1 (deriv (phi W γ t)) (X t z))^4 ∂W.μ) t := by
  sorry
end SKValue

end

end OAI
end

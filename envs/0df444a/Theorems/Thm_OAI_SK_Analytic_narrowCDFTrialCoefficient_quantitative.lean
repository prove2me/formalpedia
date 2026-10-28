-- Prove2me | Theorems.Thm_OAI_SK_Analytic_narrowCDFTrialCoefficient_quantitative
-- name    : OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:59:21.593454+00:00
-- url     : https://prove2.me/theorems/93216984-6915-4b84-91cd-2363360aae19
-- title:
--   OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative` of [lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowNegativeCoefficient.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowNegativeCoefficient.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped NNReal Topology`, `open MeasureTheory ProbabilityTheory Filter Set`):
--
--   ```lean
--   theorem narrowCDFTrialCoefficient_quantitative {β : ℝ} (hβ : β≠0)
--       (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
--       {r h q u a θ m η : ℝ} (hh : 0< h) (hr : 0≤ r) (hrq : r≤ q) (hq : q≤1)
--       (hru : r< u) (hu : u≤1) (hΓ : ∀ s∈Icc r u,scalarCDFOverlap β α s=s)
--       (hm : 0 < m) (hmr : m≤α r) (ha : 1/2≤ a) (hθ : 0≤θ) (haθ : a+θ=1)
--       (hS : scalarCDFSusceptibilityAverage β α q=(∫ x in q..1,α x)+α q*(q-scalarCDFOverlap β α q))
--       (hdev : |q-scalarCDFOverlap β α q|≤η) :
--       narrowCDFTrialCoefficient β α r h q a θ≤
--         3*β^2*η/h+narrowCDFErrorConstant β*((α (r+h)-α (r-h))+θ^2)-
--           (β^2*m*scalarJointLossConstant β m)*θ*(q-r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.narrowCDFErrorConstant` and `OAI.SK.Analytic.scalarJointLossConstant` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.scalarCDFOverlap` (definitions bundle `OAIQ036S002` of this split); `OAI.SK.Analytic.narrowCDFTrialCoefficient` and `OAI.SK.Analytic.scalarCDFSusceptibilityAverage` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowNegativeCoefficient.lean (declaration OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative)

import Mathlib
import Definitions.Def_OAIQ036S004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrowCDFTrialCoefficient_quantitative {β : ℝ} (hβ : β≠0)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    {r h q u a θ m η : ℝ} (hh : 0< h) (hr : 0≤ r) (hrq : r≤ q) (hq : q≤1)
    (hru : r< u) (hu : u≤1) (hΓ : ∀ s∈Icc r u,scalarCDFOverlap β α s=s)
    (hm : 0 < m) (hmr : m≤α r) (ha : 1/2≤ a) (hθ : 0≤θ) (haθ : a+θ=1)
    (hS : scalarCDFSusceptibilityAverage β α q=(∫ x in q..1,α x)+α q*(q-scalarCDFOverlap β α q))
    (hdev : |q-scalarCDFOverlap β α q|≤η) :
    narrowCDFTrialCoefficient β α r h q a θ≤
      3*β^2*η/h+narrowCDFErrorConstant β*((α (r+h)-α (r-h))+θ^2)-
        (β^2*m*scalarJointLossConstant β m)*θ*(q-r) := by
  sorry

end SK.Analytic

end
end

end OAI
end

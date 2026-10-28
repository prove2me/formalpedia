-- Prove2me | Theorems.Thm_OAI_SK_Analytic_tripleSchedule_value_expansion
-- name    : OAI.SK.Analytic.tripleSchedule_value_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T05:02:34.758875+00:00
-- url     : https://prove2.me/theorems/1eb64483-15fd-4b31-b253-47be1be80d64
-- title:
--   OAI.SK.Analytic.tripleSchedule_value_expansion: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.tripleSchedule_value_expansion` of [lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleFiniteExpansion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleFiniteExpansion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators Matrix`, `open MeasureTheory ProbabilityTheory Set`):
--
--   ```lean
--   theorem tripleSchedule_value_expansion (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
--       (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
--       (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
--       {a δ : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
--       (hsmall : a*(4*weightedVariance w+(2*weightedAbsCross w)^2)≤1/2) :
--       vectorIncrementChain (tripleSchedule δ c w t) (fun x => ∑ u,scalarSpinTerminal (x u)) 0≤
--         3*scalarIncrementChain (c++weightedUnderlying w++t) scalarSpinTerminal 0+
--         δ^2*tripleBaseQuadratic c w t+tripleExpansionConstant a*|δ|^3
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.weightedAbsCross`, `OAI.SK.Analytic.weightedUnderlying` and `OAI.SK.Analytic.weightedVariance` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.scalarSpinTerminal` and `OAI.SK.Analytic.tripleExpansionConstant` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.scalarIncrementChain` and `OAI.SK.Analytic.vectorIncrementChain` (definitions bundle `OAIQ036S004` of this split); `OAI.SK.Analytic.tripleSchedule` (definitions bundle `OAIQ036S005` of this split); `OAI.SK.Analytic.tripleBaseQuadratic` (definitions bundle `OAIQ036S006` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.tripleConstrainedPressure_quadratic` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleFiniteExpansion.lean (declaration OAI.SK.Analytic.tripleSchedule_value_expansion)

import Mathlib
import Definitions.Def_OAIQ036S005
import Definitions.Def_OAIQ036S006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem tripleSchedule_value_expansion (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    {a δ : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
    (hsmall : a*(4*weightedVariance w+(2*weightedAbsCross w)^2)≤1/2) :
    vectorIncrementChain (tripleSchedule δ c w t) (fun x => ∑ u,scalarSpinTerminal (x u)) 0≤
      3*scalarIncrementChain (c++weightedUnderlying w++t) scalarSpinTerminal 0+
      δ^2*tripleBaseQuadratic c w t+tripleExpansionConstant a*|δ|^3 := by
  sorry

end SK.Analytic

end
end

end OAI
end

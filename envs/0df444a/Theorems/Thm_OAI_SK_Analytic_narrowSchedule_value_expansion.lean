-- Prove2me | Theorems.Thm_OAI_SK_Analytic_narrowSchedule_value_expansion
-- name    : OAI.SK.Analytic.narrowSchedule_value_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:58:56.569935+00:00
-- url     : https://prove2.me/theorems/b187153b-7de4-46db-9c75-cb9e8246ef61
-- title:
--   OAI.SK.Analytic.narrowSchedule_value_expansion: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.narrowSchedule_value_expansion` of [lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowFiniteExpansion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowFiniteExpansion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators Matrix`, `open MeasureTheory ProbabilityTheory Set`):
--
--   ```lean
--   theorem narrowSchedule_value_expansion (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
--       (hv : weightedUnderlying v=weightedUnderlying w)
--       (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
--       (hs : (weightedUnderlying c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
--       {a δ : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
--       (hsmall : a*(4*narrowVariance c v w+(2*narrowAbsCross c v w)^2)≤1/2) :
--       vectorIncrementChain (narrowSchedule δ c v w t) (fun x => ∑ u,scalarSpinTerminal (x u)) 0≤
--         3*scalarIncrementChain (weightedUnderlying c++weightedUnderlying w++t) scalarSpinTerminal 0+
--         δ^2*narrowBaseQuadratic c v w t+tripleExpansionConstant a*|δ|^3
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.weightedUnderlying` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.scalarSpinTerminal` and `OAI.SK.Analytic.tripleExpansionConstant` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.narrowAbsCross`, `OAI.SK.Analytic.narrowSchedule` and `OAI.SK.Analytic.narrowVariance` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Analytic.narrowBaseQuadratic`, `OAI.SK.Analytic.scalarIncrementChain` and `OAI.SK.Analytic.vectorIncrementChain` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowFiniteExpansion.lean (declaration OAI.SK.Analytic.narrowSchedule_value_expansion)

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
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem narrowSchedule_value_expansion (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (weightedUnderlying c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    {a δ : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
    (hsmall : a*(4*narrowVariance c v w+(2*narrowAbsCross c v w)^2)≤1/2) :
    vectorIncrementChain (narrowSchedule δ c v w t) (fun x => ∑ u,scalarSpinTerminal (x u)) 0≤
      3*scalarIncrementChain (weightedUnderlying c++weightedUnderlying w++t) scalarSpinTerminal 0+
      δ^2*narrowBaseQuadratic c v w t+tripleExpansionConstant a*|δ|^3 := by
  sorry

end SK.Analytic

end
end

end OAI
end

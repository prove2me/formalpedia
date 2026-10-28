-- Prove2me | Theorems.Thm_OAI_SK_Analytic_tripleConstrainedPressure_schedule
-- name    : OAI.SK.Analytic.tripleConstrainedPressure_schedule
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T05:01:45.14159+00:00
-- url     : https://prove2.me/theorems/0b09c438-ab0f-492f-ad0f-09e5e42529a2
-- title:
--   OAI.SK.Analytic.tripleConstrainedPressure_schedule: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.tripleConstrainedPressure_schedule` of [lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleScheduleEndpoint.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleScheduleEndpoint.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators Matrix`, `open MeasureTheory ProbabilityTheory Set`):
--
--   ```lean
--   theorem tripleConstrainedPressure_schedule {N : ℕ} (hN : 0<N) (β δ : ℝ)
--       (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
--       (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
--       (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
--       (ht : rawVariance (c++weightedUnderlying w++t)=1) (hg : weightedCross w=1)
--       (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))))) :
--       matrixConstrainedPressure N 3 β (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))) ≤
--         vectorIncrementChain ((tripleSchedule δ c w t).map (fun p => (p.1,β • p.2)))
--           (fun x => ∑ u,scalarSpinTerminal (x u)) 0-
--         3*β^2/4*rawPenalty (c++weightedUnderlying w++t) 0-
--         β^2*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+
--         β^2*δ^4*(weightedVariance w)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.MatrixStates`, `OAI.SK.Analytic.rawArea`, `OAI.SK.Analytic.rawPenalty`, `OAI.SK.Analytic.rawVariance`, `OAI.SK.Analytic.weightedCross`, `OAI.SK.Analytic.weightedCrossPenalty`, `OAI.SK.Analytic.weightedUnderlying` and `OAI.SK.Analytic.weightedVariance` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.scalarSpinTerminal` and `OAI.SK.Analytic.tripleGram` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.matrixConstrainedPressure` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Analytic.vectorIncrementChain` (definitions bundle `OAIQ036S004` of this split); `OAI.SK.Analytic.tripleSchedule` (definitions bundle `OAIQ036S005` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.tripleConstrainedPressure_quadratic` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleScheduleEndpoint.lean (declaration OAI.SK.Analytic.tripleConstrainedPressure_schedule)

import Mathlib
import Definitions.Def_OAIQ036S004
import Definitions.Def_OAIQ036S005

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

theorem tripleConstrainedPressure_schedule {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (ht : rawVariance (c++weightedUnderlying w++t)=1) (hg : weightedCross w=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))))) :
    matrixConstrainedPressure N 3 β (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))) ≤
      vectorIncrementChain ((tripleSchedule δ c w t).map (fun p => (p.1,β • p.2)))
        (fun x => ∑ u,scalarSpinTerminal (x u)) 0-
      3*β^2/4*rawPenalty (c++weightedUnderlying w++t) 0-
      β^2*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+
      β^2*δ^4*(weightedVariance w)^2 := by
  sorry

end SK.Analytic

end
end

end OAI
end

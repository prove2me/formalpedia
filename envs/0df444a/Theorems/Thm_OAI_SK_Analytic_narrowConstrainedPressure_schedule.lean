-- Prove2me | Theorems.Thm_OAI_SK_Analytic_narrowConstrainedPressure_schedule
-- name    : OAI.SK.Analytic.narrowConstrainedPressure_schedule
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:59:18.933687+00:00
-- url     : https://prove2.me/theorems/75af4957-5c2e-4bd1-ae99-08a77b7564df
-- title:
--   OAI.SK.Analytic.narrowConstrainedPressure_schedule: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.narrowConstrainedPressure_schedule` of [lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowScheduleEndpoint.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowScheduleEndpoint.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators Matrix`, `open MeasureTheory ProbabilityTheory Set`):
--
--   ```lean
--   theorem narrowConstrainedPressure_schedule {N : ℕ} (hN : 0<N) (β δ : ℝ)
--       (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
--       (hv : weightedUnderlying v=weightedUnderlying w) (hy : weightedCross c+weightedCross w=0)
--       (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
--       (hs : (weightedUnderlying c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
--       (ht : rawVariance (weightedUnderlying c++weightedUnderlying w++t)=1)
--       (hg : weightedCross c+weightedCross v=1)
--       (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance (weightedUnderlying c)) δ
--         (rawVariance (weightedUnderlying c++weightedUnderlying w))))) :
--       matrixConstrainedPressure N 3 β (tripleGram (rawVariance (weightedUnderlying c)) δ
--         (rawVariance (weightedUnderlying c++weightedUnderlying w))) ≤
--         vectorIncrementChain ((narrowSchedule δ c v w t).map (fun p => (p.1,β • p.2)))
--           (fun x => ∑ u,scalarSpinTerminal (x u)) 0-
--         3*β^2/4*rawPenalty (weightedUnderlying c++weightedUnderlying w++t) 0-
--         β^2*δ^2*(narrowCrossPenalty c v w+narrowVariance c v w*rawArea t)+
--         β^2*δ^4*(narrowVariance c v w)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.MatrixStates`, `OAI.SK.Analytic.rawArea`, `OAI.SK.Analytic.rawPenalty`, `OAI.SK.Analytic.rawVariance`, `OAI.SK.Analytic.weightedCross` and `OAI.SK.Analytic.weightedUnderlying` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.scalarSpinTerminal` and `OAI.SK.Analytic.tripleGram` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.matrixConstrainedPressure`, `OAI.SK.Analytic.narrowCrossPenalty`, `OAI.SK.Analytic.narrowSchedule` and `OAI.SK.Analytic.narrowVariance` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Analytic.vectorIncrementChain` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowScheduleEndpoint.lean (declaration OAI.SK.Analytic.narrowConstrainedPressure_schedule)

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

theorem narrowConstrainedPressure_schedule {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w) (hy : weightedCross c+weightedCross w=0)
    (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (weightedUnderlying c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (ht : rawVariance (weightedUnderlying c++weightedUnderlying w++t)=1)
    (hg : weightedCross c+weightedCross v=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance (weightedUnderlying c)) δ
      (rawVariance (weightedUnderlying c++weightedUnderlying w))))) :
    matrixConstrainedPressure N 3 β (tripleGram (rawVariance (weightedUnderlying c)) δ
      (rawVariance (weightedUnderlying c++weightedUnderlying w))) ≤
      vectorIncrementChain ((narrowSchedule δ c v w t).map (fun p => (p.1,β • p.2)))
        (fun x => ∑ u,scalarSpinTerminal (x u)) 0-
      3*β^2/4*rawPenalty (weightedUnderlying c++weightedUnderlying w++t) 0-
      β^2*δ^2*(narrowCrossPenalty c v w+narrowVariance c v w*rawArea t)+
      β^2*δ^4*(narrowVariance c v w)^2 := by
  sorry

end SK.Analytic

end
end

end OAI
end

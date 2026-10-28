-- Prove2me | Theorems.Thm_OAI_SK_Analytic_tripleConstrainedPressure_quadratic
-- name    : OAI.SK.Analytic.tripleConstrainedPressure_quadratic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T05:02:09.083656+00:00
-- url     : https://prove2.me/theorems/990da8c0-3e1e-414a-af13-917850869e08
-- title:
--   OAI.SK.Analytic.tripleConstrainedPressure_quadratic: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.tripleConstrainedPressure_quadratic` of [lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleQuadraticPressure.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleQuadraticPressure.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators Matrix`, `open MeasureTheory ProbabilityTheory Set`):
--
--   ```lean
--   theorem tripleConstrainedPressure_quadratic {N : ℕ} (hN : 0<N) (β δ : ℝ)
--       (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
--       (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
--       (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
--       (ht : rawVariance (c++weightedUnderlying w++t)=1) (hg : weightedCross w=1)
--       (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w)))))
--       (k : Fin (zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).length → ℝ)
--       (hk : ∀ i,0≤k i)
--       (he : ∀ i,((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get i).2.2=
--         k i*((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get i).2.1)
--       {V : ℝ} (hV : 0≤V)
--       (hactive : ∀ i,k i≠0 → scalarPrefixVariance (zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).length
--         (fun j => ((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get j).2.1) i.castSucc≤V)
--       {a : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
--       (hsmall : a*(4*β^2*weightedVariance w+(2*β^2*weightedAbsCross w)^2)≤1/2) :
--       matrixConstrainedPressure N 3 β (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))) ≤
--         3*(scalarIncrementChain (scaleIncrementChain β (c++weightedUnderlying w++t)) scalarSpinTerminal 0-
--           β^2/4*rawPenalty (c++weightedUnderlying w++t) 0)+
--         δ^2*tripleQuadraticCoefficient β V c w t+
--         tripleExpansionConstant a*|δ|^3+β^2*δ^4*(weightedVariance w)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.MatrixStates`, `OAI.SK.Analytic.rawPenalty`, `OAI.SK.Analytic.rawVariance`, `OAI.SK.Analytic.scaleIncrementChain`, `OAI.SK.Analytic.weightedAbsCross`, `OAI.SK.Analytic.weightedCross`, `OAI.SK.Analytic.weightedUnderlying`, `OAI.SK.Analytic.weightedVariance` and `OAI.SK.Analytic.zeroWeightChain` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.scalarPrefixVariance`, `OAI.SK.Analytic.scalarSpinTerminal`, `OAI.SK.Analytic.tripleExpansionConstant` and `OAI.SK.Analytic.tripleGram` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.matrixConstrainedPressure` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Analytic.scalarIncrementChain` (definitions bundle `OAIQ036S004` of this split); `OAI.SK.Analytic.tripleQuadraticCoefficient` (definitions bundle `OAIQ036S006` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.signed_small_scale` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleQuadraticPressure.lean (declaration OAI.SK.Analytic.tripleConstrainedPressure_quadratic)

import Mathlib
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

theorem tripleConstrainedPressure_quadratic {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (ht : rawVariance (c++weightedUnderlying w++t)=1) (hg : weightedCross w=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w)))))
    (k : Fin (zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).length → ℝ)
    (hk : ∀ i,0≤k i)
    (he : ∀ i,((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get i).2.2=
      k i*((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get i).2.1)
    {V : ℝ} (hV : 0≤V)
    (hactive : ∀ i,k i≠0 → scalarPrefixVariance (zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).length
      (fun j => ((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get j).2.1) i.castSucc≤V)
    {a : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
    (hsmall : a*(4*β^2*weightedVariance w+(2*β^2*weightedAbsCross w)^2)≤1/2) :
    matrixConstrainedPressure N 3 β (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))) ≤
      3*(scalarIncrementChain (scaleIncrementChain β (c++weightedUnderlying w++t)) scalarSpinTerminal 0-
        β^2/4*rawPenalty (c++weightedUnderlying w++t) 0)+
      δ^2*tripleQuadraticCoefficient β V c w t+
      tripleExpansionConstant a*|δ|^3+β^2*δ^4*(weightedVariance w)^2 := by
  sorry

end SK.Analytic

end
end

end OAI
end

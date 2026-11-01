-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_prob_eq_s53
-- name    : OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:45:01.872581+00:00
-- url     : https://prove2.me/theorems/184cf1bc-a042-46f3-9252-77e8910fe0de
-- title:
--   OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq` of [lean/OAI/Combinatorics/KMedian/Sparse/SparseEnumeratedMixture.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseEnumeratedMixture.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseEnumeratedBatch`, with `open Finset`):
--
--   ```lean
--   theorem prob_eq_s53 (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
--       (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
--       (R : Finset E → Prop) [DecidablePred R] :
--       (law enum Z C p q hp hq).real.prob R=
--         (1/2)*(SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hp)).real.prob
--           (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
--         (1/2)*(SparseEnumeratedBernoulli.law enum q hq).real.prob
--           (fun ω => R (PhysicalBatchLaw.unbalanced Z ω))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PhysicalBatchLaw.unbalanced` (definitions bundle `OAIQ053K011` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.PhysicalBatchLaw.balanced` (definitions bundle `OAIQ053K026` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ053K039` of this split); `OAI.MetricKMedian.SparseEnumeratedBernoulli.law` (definitions bundle `OAIQ053K047` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseEnumeratedMixture.lean (declaration OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq)

import Mathlib
import Definitions.Def_OAIQ053K047

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem prob_eq_s53 (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (R : Finset E → Prop) [DecidablePred R] :
    (law enum Z C p q hp hq).real.prob R=
      (1/2)*(SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hp)).real.prob
        (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
      (1/2)*(SparseEnumeratedBernoulli.law enum q hq).real.prob
        (fun ω => R (PhysicalBatchLaw.unbalanced Z ω)) := by
  sorry

end MetricKMedian.SparseEnumeratedBatch
end
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Reduction_CloseCenters_completionSet_spec_s53
-- name    : OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:37:50.029207+00:00
-- url     : https://prove2.me/theorems/fe060577-00fe-4868-9bac-02c15c3da995
-- title:
--   OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec` of [lean/OAI/Combinatorics/KMedian/Reduction/RationalCompletion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/RationalCompletion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Reduction.CloseCenters`, with `open Finset`):
--
--   ```lean
--   theorem completionSet_spec_s53 (C : CloseCenters I G O (δ:ℝ)) (hδ : 0 ≤ (δ:ℝ))
--       (hsmall : (δ:ℝ) ≤ 1/6) (hO : O.Nonempty) (F : Finset (Fin I.n)) (hOF : O ⊆ F)
--       (r : Fin I.n → ℚ) (hr : ∀ t, C.radius t=(r t.val:ℝ)) :
--       let S := completionSet I F C.backup G r δ
--       S ⊆ F ∧ S.Nonempty ∧ S.card ≤ O.card ∧ cost I S ≤ (1+12*(δ:ℝ))*cost I O
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Reduction.CloseCenters` and `OAI.MetricKMedian.Reduction.CloseCenters.backup` (definitions bundle `OAIQ053K027` of this split); `OAI.MetricKMedian.Reduction.completionSet` (definitions bundle `OAIQ053K037` of this split); `OAI.MetricKMedian.Instance` and `OAI.MetricKMedian.cost` (the published bundle `Def_KMedianThreshold`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Reduction.completion_branch_exists_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/RationalCompletion.lean (declaration OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec)

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K037

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

namespace CloseCenters
variable {G O : Finset (Fin I.n)} {δ : ℚ}

attribute [local instance] OAI.MetricKMedian.Reduction.instPseudoMetricSpaceFinN_1
theorem completionSet_spec_s53 (C : CloseCenters I G O (δ:ℝ)) (hδ : 0 ≤ (δ:ℝ))
    (hsmall : (δ:ℝ) ≤ 1/6) (hO : O.Nonempty) (F : Finset (Fin I.n)) (hOF : O ⊆ F)
    (r : Fin I.n → ℚ) (hr : ∀ t, C.radius t=(r t.val:ℝ)) :
    let S := completionSet I F C.backup G r δ
    S ⊆ F ∧ S.Nonempty ∧ S.card ≤ O.card ∧ cost I S ≤ (1+12*(δ:ℝ))*cost I O := by
  sorry

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end

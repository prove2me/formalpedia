-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_step_correct_s238
-- name    : OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:13.312429+00:00
-- url     : https://prove2.me/theorems/cc9c57fb-c4b3-427b-adff-ced98a24a67e
-- title:
--   OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledResolve.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledResolve.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalCoupledMerge`, with `open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing`):
--
--   ```lean
--   lemma step_correct_s238 (loc : Fin d → V) (distance : V → Fin d → ℚ)
--       (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
--       (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision q n k : ℕ) (s : State V)
--       (h : Certified loc F v eta lo hi q (n+1) k s)
--       (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
--       (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
--       (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
--       (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
--       (step loc distance F v M N precision q n k s).Correct loc F v eta lo hi q n k
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Certified`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Outcome.Correct` (definitions bundle `Q238K031` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_correct_s238` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledResolve.lean (declaration OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct)

import Mathlib
import Definitions.Def_Q238K031

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma step_correct_s238 (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision q n k : ℕ) (s : State V)
    (h : Certified loc F v eta lo hi q (n+1) k s)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    (step loc distance F v M N precision q n k s).Correct loc F v eta lo hi q n k := by
  sorry

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

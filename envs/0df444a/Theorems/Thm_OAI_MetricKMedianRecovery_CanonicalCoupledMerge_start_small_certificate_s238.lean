-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_start_small_certificate_s238
-- name    : OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:56:18.435185+00:00
-- url     : https://prove2.me/theorems/a149de3a-13b4-44dc-a767-db7620fe621f
-- title:
--   OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialAuto.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialAuto.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalCoupledMerge`, with `open RationalLeaves PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant PhaseMergeCertificate HistoryPhaseBound`):
--
--   ```lean
--   lemma start_small_certificate_s238 (loc : Fin d→V) (distance : V→Fin d→ℚ)
--       (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
--       (v lo M : ℚ) (N precision k : ℕ) (o : Output V)
--       (he : start loc distance F v lo M N precision
--         (limit v ((M:ℝ)+8*(d:ℝ)*(M:ℝ))+1) k=.small o)
--       (hd : 0<d) (hF : F.Nonempty) (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6)
--       (hlo : 0<lo) (hM : 0<M) (hlohi : lo≤8*(d:ℚ)*M)
--       (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
--       o.project⊆F ∧ o.project.Nonempty ∧ o.project.card≤k ∧
--       ∃ (Q : ℝ) (alpha : Fin d→ℝ), 0≤Q ∧ (∑ j,nearestDistance (loc j) o.project)≤Q ∧
--         PhaseOriginalLedger.Dual loc F v lo alpha ∧ (1-3*(v:ℝ))*Q≤∑ j,alpha j
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.nearestDistance` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.HistoryPhaseBound.limit` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.PhaseOriginalLedger.Dual` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Output` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Output.project` (definitions bundle `Q238K027` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start` (definitions bundle `Q238K031` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialAuto.lean (declaration OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate)

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
open RationalLeaves PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant PhaseMergeCertificate HistoryPhaseBound
variable {V : Type*} [LinearOrder V] {d : ℕ}
variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric
lemma start_small_certificate_s238 (loc : Fin d→V) (distance : V→Fin d→ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lo M : ℚ) (N precision k : ℕ) (o : Output V)
    (he : start loc distance F v lo M N precision
      (limit v ((M:ℝ)+8*(d:ℝ)*(M:ℝ))+1) k=.small o)
    (hd : 0<d) (hF : F.Nonempty) (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6)
    (hlo : 0<lo) (hM : 0<M) (hlohi : lo≤8*(d:ℚ)*M)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    o.project⊆F ∧ o.project.Nonempty ∧ o.project.card≤k ∧
    ∃ (Q : ℝ) (alpha : Fin d→ℝ), 0≤Q ∧ (∑ j,nearestDistance (loc j) o.project)≤Q ∧
      PhaseOriginalLedger.Dual loc F v lo alpha ∧ (1-3*(v:ℝ))*Q≤∑ j,alpha j := by
  sorry
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_initialHistory_spec_s238
-- name    : OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:44:53.366274+00:00
-- url     : https://prove2.me/theorems/ff9e7c44-8b35-4f2d-a959-c80e0ec36565
-- title:
--   OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledInitial.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledInitial.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalCoupledMerge`, with `open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing`):
--
--   ```lean
--   lemma initialHistory_spec_s238 (loc : Fin d → V) (distance : V → Fin d → ℚ)
--       (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
--       (v lam : ℚ) (total : ℕ) (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) :
--       Runs (fun j=>original (loc j)) (F.image original) ∅ ∅ v lam 0 total
--         (initialHistory loc distance F v lam total)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.metric` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Runs` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238K017` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory` (definitions bundle `Q238K027` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_correct_s238` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledInitial.lean (declaration OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec)

import Mathlib
import Definitions.Def_Q238K027

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

lemma initialHistory_spec_s238 (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lam : ℚ) (total : ℕ) (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) :
    Runs (fun j=>original (loc j)) (F.image original) ∅ ∅ v lam 0 total
      (initialHistory loc distance F v lam total) := by
  sorry

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

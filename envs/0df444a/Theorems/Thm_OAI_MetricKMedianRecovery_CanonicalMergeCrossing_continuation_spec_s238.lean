-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergeCrossing_continuation_spec_s238
-- name    : OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:30:11.001196+00:00
-- url     : https://prove2.me/theorems/9d94f08b-f846-434c-b266-060da86b6c68
-- title:
--   OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/MergeCross.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/MergeCross.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalMergeCrossing`, with `open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing`):
--
--   ```lean
--   lemma continuation_spec_s238 {m d : ℕ} [PseudoMetricSpace (Fin m)]
--       (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
--       (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
--       (F B Q : Finset (Fin m)) (v lam : ℚ)
--       (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (q n : ℕ) (hQ : Q⊆F∪B) :
--       Runs loc F B Q v lam q n (continuation distance F v lam q n Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Runs` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238` and `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/MergeCross.lean (declaration OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec)

import Mathlib
import Definitions.Def_Q238K022

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma continuation_spec_s238 {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F B Q : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (q n : ℕ) (hQ : Q⊆F∪B) :
    Runs loc F B Q v lam q n (continuation distance F v lam q n Q) := by
  sorry

end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

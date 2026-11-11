-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_HistoryCompatibleCertificate_compatible_certificate_s238
-- name    : OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:22:23.897113+00:00
-- url     : https://prove2.me/theorems/dbfc4c55-c946-40b8-9ddd-f8f00fe4ad58
-- title:
--   OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/FinalBudgetPos.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/FinalBudgetPos.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.HistoryCompatibleCertificate`):
--
--   ```lean
--   theorem compatible_certificate_s238 (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
--       (T : List (List X)) (hFB : Disjoint F B)
--       (hfar : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
--       (h : PhaseHistoryTransfer.History loc F B v lam eta 0 ∅ T)
--       (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^T.length)
--         (PhaseHistoryTransfer.after ∅ T) j)
--       (hv : 0 < v) (hv1 : v < 1/6) (hlam : 0 < lam) :
--       ∃ alpha : D → ℝ,
--         (∀ j, 0 < alpha j) ∧
--         (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
--         ((1-3*v)*(∑ j, nearestDistance (loc j) (PhaseHistoryTransfer.after ∅ T)) +
--           ((PhaseHistoryTransfer.after ∅ T ∩ F).card:ℝ)*(lam-(Fintype.card D:ℝ)*eta) ≤
--             ∑ j, alpha j) ∧
--         (∀ (C : Finset D), C.Nonempty → ∀ i ∈ F, ∀ b : ℝ, 0 < b →
--           0 < (∑ j ∈ C, dist i (loc j)) →
--           lam ≤ b*(∑ j ∈ C, dist i (loc j)) →
--           v^2 ≤ strictnessGap b/(6*(b+2)) →
--           (∑ j ∈ C, alpha j) ≤ lam+(2-strictnessGap b/2)*(∑ j ∈ C, dist i (loc j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.activeAt` and `OAI.MetricKMedianRecovery.nearestDistance` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.strictnessGap` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.PhaseHistoryTransfer.after` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.PhaseHistoryTransfer.History` (definitions bundle `Q238K014` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/FinalBudgetPos.lean (declaration OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate)

import Mathlib
import Definitions.Def_Q238K014

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.HistoryCompatibleCertificate
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem compatible_certificate_s238 (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
    (T : List (List X)) (hFB : Disjoint F B)
    (hfar : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (h : PhaseHistoryTransfer.History loc F B v lam eta 0 ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^T.length)
      (PhaseHistoryTransfer.after ∅ T) j)
    (hv : 0 < v) (hv1 : v < 1/6) (hlam : 0 < lam) :
    ∃ alpha : D → ℝ,
      (∀ j, 0 < alpha j) ∧
      (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
      ((1-3*v)*(∑ j, nearestDistance (loc j) (PhaseHistoryTransfer.after ∅ T)) +
        ((PhaseHistoryTransfer.after ∅ T ∩ F).card:ℝ)*(lam-(Fintype.card D:ℝ)*eta) ≤
          ∑ j, alpha j) ∧
      (∀ (C : Finset D), C.Nonempty → ∀ i ∈ F, ∀ b : ℝ, 0 < b →
        0 < (∑ j ∈ C, dist i (loc j)) →
        lam ≤ b*(∑ j ∈ C, dist i (loc j)) →
        v^2 ≤ strictnessGap b/(6*(b+2)) →
        (∑ j ∈ C, alpha j) ≤ lam+(2-strictnessGap b/2)*(∑ j ∈ C, dist i (loc j))) := by
  sorry

end MetricKMedianRecovery.HistoryCompatibleCertificate

end OAI
end

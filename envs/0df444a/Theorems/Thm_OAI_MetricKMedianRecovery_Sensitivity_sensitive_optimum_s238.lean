-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Sensitivity_sensitive_optimum_s238
-- name    : OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:24:24.520702+00:00
-- url     : https://prove2.me/theorems/52c80c3b-5443-4c6a-963e-9ed4775c923f
-- title:
--   OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/OptimumClusterSeparation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/OptimumClusterSeparation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Sensitivity`, with `open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring`):
--
--   ```lean
--   theorem sensitive_optimum_s238 (F D : Finset V) (hF : F.Nonempty) (k L : ℕ)
--       (hL : 0 < L) (hk : 2*L < k) (hkF : k ≤ F.card)
--       (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
--       (hsens : (1+xi)*optimum F D k < optimum F D (k-2*L)) :
--       ∃ h : ℕ, k-2*L < h ∧ h ≤ k ∧
--         (1+xi/(4*L))*optimum F D h ≤ optimum F D (h-1) ∧
--         optimum F D h ≤ (1+xi)*optimum F D k ∧
--         ∃ O : Finset V, ∃ hO : O.Nonempty, O ⊆ F ∧ O.card = h ∧
--           cost D O = optimum F D h ∧
--           ∀ i ∈ O, (xi/(4*L))*cost D O ≤
--             ((cluster D (nearest O hO) i).card:ℝ)*separation O i
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Anchoring.cluster`, `OAI.MetricKMedianRecovery.Anchoring.separation` and `OAI.MetricKMedianRecovery.LocalSearch.nearest` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.LocalSearch.cost` and `OAI.MetricKMedianRecovery.LocalSearch.optimum` (definitions bundle `Q238K015` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/OptimumClusterSeparation.lean (declaration OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum)

import Mathlib
import Definitions.Def_Q238K015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sensitivity
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [MetricSpace V] [DecidableEq V]

theorem sensitive_optimum_s238 (F D : Finset V) (hF : F.Nonempty) (k L : ℕ)
    (hL : 0 < L) (hk : 2*L < k) (hkF : k ≤ F.card)
    (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hsens : (1+xi)*optimum F D k < optimum F D (k-2*L)) :
    ∃ h : ℕ, k-2*L < h ∧ h ≤ k ∧
      (1+xi/(4*L))*optimum F D h ≤ optimum F D (h-1) ∧
      optimum F D h ≤ (1+xi)*optimum F D k ∧
      ∃ O : Finset V, ∃ hO : O.Nonempty, O ⊆ F ∧ O.card = h ∧
        cost D O = optimum F D h ∧
        ∀ i ∈ O, (xi/(4*L))*cost D O ≤
          ((cluster D (nearest O hO) i).card:ℝ)*separation O i := by
  sorry

end MetricKMedianRecovery.Sensitivity

end OAI
end

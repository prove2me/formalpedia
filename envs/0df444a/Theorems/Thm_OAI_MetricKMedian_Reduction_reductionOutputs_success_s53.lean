-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Reduction_reductionOutputs_success_s53
-- name    : OAI.MetricKMedian.Reduction.reductionOutputs_success_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:38:14.635487+00:00
-- url     : https://prove2.me/theorems/67fcb3ff-e145-4228-9ab5-03505495f6f6
-- title:
--   OAI.MetricKMedian.Reduction.reductionOutputs_success_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Reduction.reductionOutputs_success` of [lean/OAI/Combinatorics/KMedian/Reduction/BudgetReduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/BudgetReduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Reduction`, with `open Finset`):
--
--   ```lean
--   theorem reductionOutputs_success_s53
--       (pseudo : (I : Instance) → Finset (Fin I.n)) (α η : ℝ) (δ : ℚ) (c a b : ℕ)
--       (hc : 0 < c) (hδ : 0 < (δ:ℝ)) (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η)
--       (hfactor : 1+12*(δ:ℝ) ≤ α+η)
--       (ha : (3/2:ℝ) ≤ a*((δ:ℝ)*η/(2*c)))
--       (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ))
--       (hpseudo : ∀ I, pseudo I ⊆ I.facilities ∧ (pseudo I).Nonempty ∧
--         (pseudo I).card ≤ I.k+c ∧ cost I (pseudo I) ≤ α*optimum I)
--       (I : Instance) (hopt : 0 < optimum I) :
--       ∃ S ∈ reductionOutputs pseudo I δ c a b,
--         S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*optimum I
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Reduction.reductionOutputs` (definitions bundle `OAIQ053K037` of this split); `OAI.MetricKMedian.Instance`, `OAI.MetricKMedian.cost` and `OAI.MetricKMedian.optimum` (the published bundle `Def_KMedianThreshold`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.factor_above_threshold_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/BudgetReduction.lean (declaration OAI.MetricKMedian.Reduction.reductionOutputs_success)

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K037

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Reduction

theorem reductionOutputs_success_s53
    (pseudo : (I : Instance) → Finset (Fin I.n)) (α η : ℝ) (δ : ℚ) (c a b : ℕ)
    (hc : 0 < c) (hδ : 0 < (δ:ℝ)) (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η)
    (hfactor : 1+12*(δ:ℝ) ≤ α+η)
    (ha : (3/2:ℝ) ≤ a*((δ:ℝ)*η/(2*c)))
    (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ))
    (hpseudo : ∀ I, pseudo I ⊆ I.facilities ∧ (pseudo I).Nonempty ∧
      (pseudo I).card ≤ I.k+c ∧ cost I (pseudo I) ≤ α*optimum I)
    (I : Instance) (hopt : 0 < optimum I) :
    ∃ S ∈ reductionOutputs pseudo I δ c a b,
      S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*optimum I := by
  sorry

end Reduction
end MetricKMedian
end
end

end OAI
end

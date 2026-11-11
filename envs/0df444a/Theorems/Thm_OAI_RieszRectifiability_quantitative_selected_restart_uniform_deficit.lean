-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_quantitative_selected_restart_uniform_deficit
-- name    : OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:39.846776+00:00
-- url     : https://prove2.me/theorems/b034d547-5237-4578-9570-779acbfc75c4
-- title:
--   OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit` of [lean/OAI/Analysis/RieszRectifiability/Uniformity/RestartBudgets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Uniformity/RestartBudgets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem quantitative_selected_restart_uniform_deficit {p d : ℕ} (hnd : p + 1 ≤ d)
--       (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
--       (ζ : ℝ) (hζ : 0 < ζ) :
--       ∃ δ : ℝ, 0 < δ ∧ ∃ b : ℕ, 0 < b ∧
--         ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
--         GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
--           AdmissibleRadius μ (latticeRadius R k / 8) →
--           let Bad := fun i : SupportCellDescendant μ R hR k z =>
--             ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
--           ∀ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
--             (step : ℝ≥0 → ℝ≥0),
--             HasSelectedRestartAssembly (p + 1) Bad E step →
--             (∀ q, μ (selectedRestartRemainder Bad q.val (E q)) ≤ ENNReal.ofReal δ * μ q.val.cell) →
--             ∃ g : ball (0 : Ambient (p + 1)) (latticeRadius R k) → Ambient d,
--               LipschitzWith (badBudgetChartConstant step b) g ∧
--               Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
--               μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
--                 ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.HasSelectedRestartAssembly`, `OAI.RieszRectifiability.SupportCellDescendant`, `OAI.RieszRectifiability.badBudgetChartConstant`, `OAI.RieszRectifiability.bilateralBeta`, `OAI.RieszRectifiability.cellRestartsAfter`, `OAI.RieszRectifiability.cleanSupportCell`, `OAI.RieszRectifiability.latticeRadius`, `OAI.RieszRectifiability.selectedRestartRemainder`, `OAI.RieszRectifiability.supportLatticeNets`, `OAI.RieszRectifiability.SeparatedCover`, `OAI.RieszRectifiability.SupportCellDescendant.cell` and `OAI.RieszRectifiability.SupportCellDescendant.radius` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.ADRegularWithConstant`, `OAI.RieszRectifiability.AdmissibleRadius`, `OAI.RieszRectifiability.Ambient` and `OAI.RieszRectifiability.RieszL2BoundedWithConstant` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Uniformity/RestartBudgets.lean (declaration OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit)

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

theorem quantitative_selected_restart_uniform_deficit {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : ℕ, 0 < b ∧
      ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Bad := fun i : SupportCellDescendant μ R hR k z =>
          ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
        ∀ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
          (step : ℝ≥0 → ℝ≥0),
          HasSelectedRestartAssembly (p + 1) Bad E step →
          (∀ q, μ (selectedRestartRemainder Bad q.val (E q)) ≤ ENNReal.ofReal δ * μ q.val.cell) →
          ∃ g : ball (0 : Ambient (p + 1)) (latticeRadius R k) → Ambient d,
            LipschitzWith (badBudgetChartConstant step b) g ∧
            Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
            μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
              ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  sorry

end
end RieszRectifiability

end OAI
end

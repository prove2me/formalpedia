-- Prove2me | Theorems.Thm_MultiPeriod_costGo_le_VGo_add
-- name    : MultiPeriod.costGo_le_VGo_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:10:11.869934+00:00
-- url     : https://prove2.me/theorems/c384f7aa-aaf3-4770-bea5-83f2703f7a33
-- title:
--   Multi Period: cost Go le VGo add
-- statement:
--   L4: over `k` remaining periods (with `t + k = T`), the ε-optimal
--       strategy overshoots the Bellman value by at most `k·ε`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriod.lean#L145-L184
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriod.lean#L145-L184

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_BicausalOT_MultiPeriod
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable (X Y : ℕ → Type*)
variable {X Y}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
variable {κμ κν}
variable (κμ κν)

theorem MultiPeriod.costGo_le_VGo_add (T : ℕ)
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (γε : Strat X Y) (hmem : ∀ t h, γε t h ∈ Feas κμ κν t h)
    {ε : ℝ≥0∞}
    (hopt : ∀ t (h : PairHist X Y t),
      ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γε t h)
        ≤ (⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
            (_ : γm ∈ Feas κμ κν t h),
            ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) + ε) :
    ∀ (k t : ℕ), t + k = T → ∀ h : PairHist X Y t,
      costGo c γε k t h ≤ VGo c κμ κν k t h + (k : ℝ≥0∞) * ε
  := by sorry

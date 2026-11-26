-- Prove2me | Theorems.Thm_MultiPeriod_VGo_le_pointwise
-- name    : MultiPeriod.VGo_le_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:09:50.187596+00:00
-- url     : https://prove2.me/theorems/dde9fd6f-3796-4eeb-96f5-76e4afb71c18
-- title:
--   Multi Period: VGo le pointwise
-- statement:
--   L1: pointwise Bellman bound at any feasible one-step plan.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriod.lean#L98-L104
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriod.lean#L98-L104

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

theorem MultiPeriod.VGo_le_pointwise {t k : ℕ} {h : PairHist X Y t}
    {γm : Measure (X (t + 1) × Y (t + 1))} (hγ : γm ∈ Feas κμ κν t h) :
    VGo c κμ κν (k + 1) t h
      ≤ c t h + ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γm := by sorry

-- Prove2me | Theorems.Thm_MultiPeriod_Feas_measure_univ
-- name    : MultiPeriod.Feas.measure_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:09:41.618888+00:00
-- url     : https://prove2.me/theorems/9183c8c7-365a-54ff-b866-ae6db35f69d1
-- title:
--   Feas: measure univ
-- statement:
--   L0: feasible one-step plans are probability measures when the
--       conditional marginals are.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriod.lean#L86-L95
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriod.lean#L86-L95

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

theorem MultiPeriod.Feas.measure_univ
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    {t : ℕ} {h : PairHist X Y t}
    {γm : Measure (X (t + 1) × Y (t + 1))} (hγ : γm ∈ Feas κμ κν t h) :
    γm Set.univ = 1 := by sorry

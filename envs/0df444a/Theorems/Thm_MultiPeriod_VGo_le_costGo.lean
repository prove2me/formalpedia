-- Prove2me | Theorems.Thm_MultiPeriod_VGo_le_costGo
-- name    : MultiPeriod.VGo_le_costGo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:09:48.520364+00:00
-- url     : https://prove2.me/theorems/2fd22e78-aa24-5196-9718-8edbf81c7b7a
-- title:
--   Multi Period: VGo le cost Go
-- statement:
--   L2: the Bellman value bounds the cost of every feasible strategy,
--       pointwise in the history. Backward induction on the time to go.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriod.lean#L108-L117
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriod.lean#L108-L117

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

theorem MultiPeriod.VGo_le_costGo (γ : Strat X Y)
    (hfeas : ∀ t h, γ t h ∈ Feas κμ κν t h) :
    ∀ (k t : ℕ) (h : PairHist X Y t),
      VGo c κμ κν k t h ≤ costGo c γ k t h
  := by sorry

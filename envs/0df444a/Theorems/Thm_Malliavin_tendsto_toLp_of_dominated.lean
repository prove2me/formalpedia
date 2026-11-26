-- Prove2me | Theorems.Thm_Malliavin_tendsto_toLp_of_dominated
-- name    : Malliavin.tendsto_toLp_of_dominated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:35.805332+00:00
-- url     : https://prove2.me/theorems/bee9eb0b-19df-438f-ab01-e3c6d807e29d
-- title:
--   Malliavin: tendsto to Lp of dominated
-- statement:
--   **Dominated convergence in `L²`.**
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L145-L169
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L145-L169

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2
open Malliavin
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

theorem Malliavin.tendsto_toLp_of_dominated {f : ℕ → α → E} {g : α → E} (hf : ∀ n, MemLp (f n) 2 μ)
    (hg : MemLp g 2 μ) {bound : α → ℝ} (hbound : Integrable bound μ)
    (h : ∀ n, ∀ᵐ x ∂μ, ‖f n x - g x‖ ^ 2 ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by sorry

-- Prove2me | Theorems.Thm_MeasureTheory_Lp_coeFn_finset_sum
-- name    : MeasureTheory.Lp.coeFn_finset_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:48.957244+00:00
-- url     : https://prove2.me/theorems/7fce72dd-574f-49b8-8ed9-f82fa625799a
-- title:
--   Lp: coe Fn finset sum
-- statement:
--   Coercion of a finite sum in `Lp` is a.e. the sum of the coercions.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L259-L268
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L259-L268

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ}
omit [NormedSpace ℝ E]

theorem MeasureTheory.Lp.coeFn_finset_sum {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {p : ℝ≥0∞} {ι : Type*} (s : Finset ι) (g : ι → Lp E p ν) :
    ⇑(∑ i ∈ s, g i) =ᵐ[ν] ∑ i ∈ s, ⇑(g i) := by sorry

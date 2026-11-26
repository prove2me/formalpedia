-- Prove2me | Theorems.Thm_Malliavin_coeFn_symmetrizeL
-- name    : Malliavin.coeFn_symmetrizeL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:20.877454+00:00
-- url     : https://prove2.me/theorems/3ea2390c-75db-55fd-87b9-baf60579e5b6
-- title:
--   Malliavin: coe Fn symmetrize L
-- statement:
--   `symmetrizeL` is a.e. the pointwise symmetrization of a representative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L302-L312
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L302-L312

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

theorem Malliavin.coeFn_symmetrizeL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    ⇑(symmetrizeL E (μ := μ) n p f) =ᵐ[Measure.pi fun _ : Fin n => μ] symmetrize n ⇑f := by sorry

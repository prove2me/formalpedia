-- Prove2me | Theorems.Thm_Malliavin_measure_coord_eq_zero
-- name    : Malliavin.measure_coord_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:48:23.466137+00:00
-- url     : https://prove2.me/theorems/d8240aef-55cd-5ed5-9208-72bb60c623e7
-- title:
--   Malliavin: measure coord eq zero
-- statement:
--   For `i ≠ j`, the "hyperplane" `{t | t i = t j}` is `μ^{⊗n}`-null when `μ` has no atoms:
--   split off the coordinate `i` with `piFinSuccAbove` and apply Fubini (`Measure.prod_apply`).
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L198-L239
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L198-L239

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
variable {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Malliavin.measure_coord_eq_zero [NullSingletonClass μ] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Measure.pi (fun _ : Fin n => μ) {t : Fin n → T | t i = t j} = 0 := by sorry

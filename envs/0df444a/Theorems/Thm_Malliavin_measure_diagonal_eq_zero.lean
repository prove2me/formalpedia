-- Prove2me | Theorems.Thm_Malliavin_measure_diagonal_eq_zero
-- name    : Malliavin.measure_diagonal_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:42.875292+00:00
-- url     : https://prove2.me/theorems/fcbc2bb8-f6e8-449f-99d3-da80d7053ada
-- title:
--   Malliavin: measure diagonal eq zero
-- statement:
--   The diagonal is `μ^{⊗n}`-null when `μ` has no atoms.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L242-L246
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L242-L246

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

theorem Malliavin.measure_diagonal_eq_zero [NullSingletonClass μ] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) (diagonal T n) = 0 := by sorry

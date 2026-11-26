-- Prove2me | Theorems.Thm_Malliavin_integral_symmetrize_eq_factorial_smul
-- name    : Malliavin.integral_symmetrize_eq_factorial_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:57:07.131769+00:00
-- url     : https://prove2.me/theorems/90382245-e952-546c-a932-5e7fecd67f39
-- title:
--   Malliavin: integral symmetrize eq factorial smul
-- statement:
--   Specialisation to a symmetrized function: `∫ f̃ = n! • ∫_{Δₙ} f̃`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L359-L363
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L359-L363

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

theorem Malliavin.integral_symmetrize_eq_factorial_smul [NullSingletonClass μ] {n : ℕ} {f : (Fin n → T) → E}
    (hint : Integrable (symmetrize n f) (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, symmetrize n f t ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, symmetrize n f t ∂(Measure.pi fun _ : Fin n => μ) := by sorry

-- Prove2me | Theorems.Thm_Malliavin_integral_sq_norm_eq_factorial_smul
-- name    : Malliavin.integral_sq_norm_eq_factorial_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:57:00.402497+00:00
-- url     : https://prove2.me/theorems/a5b53ad3-f82b-48e4-ac4e-902004d858d2
-- title:
--   Malliavin: integral sq norm eq factorial smul
-- statement:
--   The `L²` form of the tiling identity: `∫ ‖g‖² = n! • ∫_{Δₙ} ‖g‖²` for symmetric `g ∈ L²`.
--   This is the identity that turns `E[Jₙ(g)²] = ‖g‖²_{L²(Δₙ)}` into `E[Iₙ(g)²] = n! ‖g‖²_{L²(Tⁿ)}`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L351-L356
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L351-L356

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
omit [NormedSpace ℝ E]

theorem Malliavin.integral_sq_norm_eq_factorial_smul [NullSingletonClass μ] {n : ℕ} {g : (Fin n → T) → E}
    (hg : IsSymmetric n g) (hg2 : MemLp g 2 (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, ‖g t‖ ^ 2 ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, ‖g t‖ ^ 2 ∂(Measure.pi fun _ : Fin n => μ) := by sorry

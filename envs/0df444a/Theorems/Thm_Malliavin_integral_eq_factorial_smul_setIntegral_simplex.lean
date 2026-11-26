-- Prove2me | Theorems.Thm_Malliavin_integral_eq_factorial_smul_setIntegral_simplex
-- name    : Malliavin.integral_eq_factorial_smul_setIntegral_simplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:26.11909+00:00
-- url     : https://prove2.me/theorems/681ea52b-9447-4e94-a8cb-1f7900a468d9
-- title:
--   Malliavin: integral eq factorial smul set Integral simplex
-- statement:
--   **Tiling identity**: for symmetric integrable `g`, `∫ g dμ^{⊗n} = n! • ∫_{Δₙ} g dμ^{⊗n}`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L274-L296
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L274-L296

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

theorem Malliavin.integral_eq_factorial_smul_setIntegral_simplex [NullSingletonClass μ] {n : ℕ}
    {g : (Fin n → T) → E} (hg : IsSymmetric n g)
    (hint : Integrable g (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, g t ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) := by sorry

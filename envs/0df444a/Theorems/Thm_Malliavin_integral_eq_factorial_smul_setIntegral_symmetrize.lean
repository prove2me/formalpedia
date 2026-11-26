-- Prove2me | Theorems.Thm_Malliavin_integral_eq_factorial_smul_setIntegral_symmetrize
-- name    : Malliavin.integral_eq_factorial_smul_setIntegral_symmetrize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:53.70483+00:00
-- url     : https://prove2.me/theorems/4b976fe6-1e66-4660-bb21-abbef4cef403
-- title:
--   Malliavin: integral eq factorial smul set Integral symmetrize
-- statement:
--   **Tiling identity, general form**: for any integrable `g`,
--   `∫ g dμ^{⊗n} = n! • ∫_{Δₙ} (symmetrize n g) dμ^{⊗n}` — the deterministic shadow of
--   `Iₙ(f) = Iₙ(f̃)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L301-L346
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L301-L346

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

theorem Malliavin.integral_eq_factorial_smul_setIntegral_symmetrize [NullSingletonClass μ] {n : ℕ}
    {g : (Fin n → T) → E} (hint : Integrable g (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, g t ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, symmetrize n g t ∂(Measure.pi fun _ : Fin n => μ) := by sorry

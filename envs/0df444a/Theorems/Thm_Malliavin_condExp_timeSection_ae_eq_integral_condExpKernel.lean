-- Prove2me | Theorems.Thm_Malliavin_condExp_timeSection_ae_eq_integral_condExpKernel
-- name    : Malliavin.condExp_timeSection_ae_eq_integral_condExpKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:51.140748+00:00
-- url     : https://prove2.me/theorems/6fa62dd5-6be1-43f5-b7f1-153253a78920
-- title:
--   Malliavin: cond Exp time Section ae eq integral cond Exp Kernel
-- statement:
--   **Pointwise conditional expectation of time sections.**  For a product-`L²` process `U` and
--   almost every time `t`, the conditional expectation of the section `U (t, ·)` given `𝓕 t` is the
--   pointwise kernel integral `ω ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) ω`.  The exceptional set of
--   times depends on the chosen representative of `U`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L58-L64
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L58-L64

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

theorem Malliavin.condExp_timeSection_ae_eq_integral_condExpKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      P[(fun ω ↦ U (t, ω)) | 𝓕 t] =ᵐ[P]
        fun ω ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) ω := by sorry

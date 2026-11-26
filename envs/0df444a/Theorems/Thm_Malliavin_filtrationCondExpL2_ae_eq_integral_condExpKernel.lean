-- Prove2me | Theorems.Thm_Malliavin_filtrationCondExpL2_ae_eq_integral_condExpKernel
-- name    : Malliavin.filtrationCondExpL2_ae_eq_integral_condExpKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:09.434309+00:00
-- url     : https://prove2.me/theorems/8d01998f-470b-418c-bb40-4bd9b80335e7
-- title:
--   Malliavin: filtration Cond Exp L2 ae eq integral cond Exp Kernel
-- statement:
--   The fixed-time conditional expectation operator of the Clark--Ocone development is,
--   almost everywhere, the integral against the disintegration kernel `condExpKernel P (𝓕 t)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L47-L52
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L47-L52

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

theorem Malliavin.filtrationCondExpL2_ae_eq_integral_condExpKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (F : RandomL2 P) :
    (filtrationCondExpL2 𝓕 t F : W → ℝ) =ᵐ[P]
      fun ω ↦ ∫ y, F y ∂condExpKernel P (𝓕 t) ω := by sorry

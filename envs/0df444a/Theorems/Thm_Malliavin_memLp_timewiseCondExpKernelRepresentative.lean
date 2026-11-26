-- Prove2me | Theorems.Thm_Malliavin_memLp_timewiseCondExpKernelRepresentative
-- name    : Malliavin.memLp_timewiseCondExpKernelRepresentative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:36.637752+00:00
-- url     : https://prove2.me/theorems/22b8a3a3-6472-41e9-9f76-241e66319410
-- title:
--   Malliavin: mem Lp timewise Cond Exp Kernel Representative
-- statement:
--   Joint predictable measurability of the timewise conditional-kernel candidate implies its
--   product-`L²` integrability.  The proof integrates the fixed-time `L²` contraction for conditional
--   expectation over time.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimewiseCondExp.lean#L174-L220
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimewiseCondExp.lean#L174-L220

import Definitions.Def_Malliavin_NaturalItoDuality
import Mathlib.Probability.Kernel.Condexp
import Definitions.Def_Malliavin_TimewiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

theorem Malliavin.memLp_timewiseCondExpKernelRepresentative
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P)
    (hpred : AEStronglyMeasurable[𝓕.predictable]
      (timewiseCondExpKernelRepresentative 𝓕 U)
      (nonnegativeLebesgueMeasure.prod P)) :
    MemLp (timewiseCondExpKernelRepresentative 𝓕 U) 2
      (nonnegativeLebesgueMeasure.prod P) := by sorry

-- Prove2me | Theorems.Thm_Malliavin_condExpKernel_predictable_ae_same_time
-- name    : Malliavin.condExpKernel_predictable_ae_same_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:26.148268+00:00
-- url     : https://prove2.me/theorems/85a94daa-6fc8-54e1-85bf-bb66ec15f703
-- title:
--   Malliavin: cond Exp Kernel predictable ae same time
-- statement:
--   A conditional-expectation kernel onto the predictable σ-algebra preserves the observed time:
--   conditionally, the output time is almost surely the input time.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L79-L107
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L79-L107

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]

theorem Malliavin.condExpKernel_predictable_ae_same_time
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    ∀ᵐ p ∂μ, ∀ᵐ q ∂condExpKernel μ 𝓕.predictable p, q.1 = p.1 := by sorry

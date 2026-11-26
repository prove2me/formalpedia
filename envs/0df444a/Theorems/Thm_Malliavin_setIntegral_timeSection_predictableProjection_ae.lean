-- Prove2me | Theorems.Thm_Malliavin_setIntegral_timeSection_predictableProjection_ae
-- name    : Malliavin.setIntegral_timeSection_predictableProjection_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:26:42.836328+00:00
-- url     : https://prove2.me/theorems/40441338-4dc6-599f-92dc-670a3455caf5
-- title:
--   Malliavin: set Integral time Section predictable Projection ae
-- statement:
--   **Sections of the predictable projection carry the conditional moments of `U`**: for every
--   `a` and every `A ∈ 𝓕 a`, for almost every time `t > a`,
--
--     `∫_A (predictableProjection 𝓕 U) (t, ·) dP = ∫_A U (t, ·) dP`.
--
--   The null set of times depends on `(a, A)`.  Together with the `𝓕 t`-measurability of the
--   sections this is the conditional-moment content of `E[Uₜ | 𝓕ₜ]` against every strictly prior
--   event.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L177-L229
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L177-L229

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
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.setIntegral_timeSection_predictableProjection_ae (U : TimeProcessL2 P) {a : ℝ≥0}
    {A : Set W} (hA : MeasurableSet[𝓕 a] A) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      ∫ ω in A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) ∂P
        = ∫ ω in A, U (t, ω) ∂P := by sorry

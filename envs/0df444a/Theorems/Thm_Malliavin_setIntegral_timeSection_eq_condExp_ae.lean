-- Prove2me | Theorems.Thm_Malliavin_setIntegral_timeSection_eq_condExp_ae
-- name    : Malliavin.setIntegral_timeSection_eq_condExp_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:10.947229+00:00
-- url     : https://prove2.me/theorems/559be16a-7a19-4a9f-ad0f-da82e20ed008
-- title:
--   Malliavin: set Integral time Section eq cond Exp ae
-- statement:
--   **Conditional-moment identification of the sections**: for every `a` and `A ∈ 𝓕 a`, for
--   almost every `t > a` the section of the predictable projection has the same integral over `A`
--   as the fixed-time conditional expectation `E[U (t, ·) | 𝓕 t]`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L235-L244
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L235-L244

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

theorem Malliavin.setIntegral_timeSection_eq_condExp_ae (U : TimeProcessL2 P) {a : ℝ≥0} {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      ∫ ω in A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) ∂P
        = ∫ ω in A, (P[(fun ω ↦ U (t, ω)) | 𝓕 t]) ω ∂P := by sorry

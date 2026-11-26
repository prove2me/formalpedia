-- Prove2me | Theorems.Thm_Malliavin_exists_representative_predictableDerivative_condExp
-- name    : Malliavin.exists_representative_predictableDerivative_condExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:16:57.931606+00:00
-- url     : https://prove2.me/theorems/4fb5fe0c-fa2a-5cca-94ea-64e833a26564
-- title:
--   Malliavin: exists representative predictable Derivative cond Exp
-- statement:
--   **The Clark--Ocone integrand is `E[Dₜ F | 𝓕_{t⁻}]`.**  Over any Clark--Ocone family the
--   integrand `predictableDerivative C F` has a predictable strongly measurable representative `G`
--   with, for almost every `t > 0`,
--
--     `G (t, ·) =ᵐ[P] E[(Dₜ F) (t, ·) | 𝓕_{t⁻}]`,
--
--   the literal pointwise conditional expectation of the time derivative given the strict past.
--   Second countability of `L²(P)` holds automatically because the family is Wiener generated.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L748-L763
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L748-L763

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
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}

theorem Malliavin.exists_representative_predictableDerivative_condExp
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | filtrationPred 𝓕 t] := by sorry

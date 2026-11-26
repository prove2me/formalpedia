-- Prove2me | Theorems.Thm_Malliavin_exists_representative_predictableDerivative_condExp_condExp
-- name    : Malliavin.exists_representative_predictableDerivative_condExp_condExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:57.855701+00:00
-- url     : https://prove2.me/theorems/50e0910d-8f8d-57d4-883f-348a777c9d81
-- title:
--   Malliavin: exists representative predictable Derivative cond Exp cond Exp
-- statement:
--   Tower form: the representative is the strict-past conditional expectation *of* the textbook
--   integrand `E[Dₜ F | 𝓕 t]`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L767-L781
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L767-L781

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

theorem Malliavin.exists_representative_predictableDerivative_condExp_condExp
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t] |
            filtrationPred 𝓕 t] := by sorry

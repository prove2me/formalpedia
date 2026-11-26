-- Prove2me | Theorems.Thm_Malliavin_exists_representative_predictableDerivative
-- name    : Malliavin.exists_representative_predictableDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:50.395705+00:00
-- url     : https://prove2.me/theorems/af4e0383-3d0b-5c8a-bb72-9e4b27ba83a3
-- title:
--   Malliavin: exists representative predictable Derivative
-- statement:
--   **The Clark--Ocone integrand, pointwise form.**  For `F ∈ 𝔻₁,₂`, the Clark--Ocone integrand
--   `predictableDerivative C F` has a representative `G` that is predictable strongly measurable,
--   whose section at every time `t` is `𝓕 t`-strongly measurable, and whose section integrals agree
--   with those of the fixed-time conditional expectation `E[(Dₜ F) | 𝓕 t]` of the time derivative
--   against every event `A ∈ 𝓕 a` for almost every `t > a`.  This is the textbook
--   `E[Dₜ F | 𝓕ₜ]` up to the uniformity of the exceptional times over test events.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L728-L738
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L728-L738

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

theorem Malliavin.exists_representative_predictableDerivative (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      (∀ t, StronglyMeasurable[𝓕 t] fun ω ↦ G (t, ω)) ∧
      ∀ (a : ℝ≥0) (A : Set W), MeasurableSet[𝓕 a] A →
        ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
          ∫ ω in A, G (t, ω) ∂P
            = ∫ ω in A,
                (P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t]) ω ∂P := by sorry

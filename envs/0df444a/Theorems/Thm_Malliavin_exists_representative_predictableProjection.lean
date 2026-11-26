-- Prove2me | Theorems.Thm_Malliavin_exists_representative_predictableProjection
-- name    : Malliavin.exists_representative_predictableProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:19.795353+00:00
-- url     : https://prove2.me/theorems/43512cce-d9f9-4067-837b-094b229787e7
-- title:
--   Malliavin: exists representative predictable Projection
-- statement:
--   **Pointwise representative of the predictable projection.**  The predictable projection of
--   `U` has a representative `G` that is strongly measurable for the predictable σ-algebra, whose
--   time section at *every* time `t` is `𝓕 t`-strongly measurable, and whose sections carry the
--   conditional moments of `U`: for every `a` and `A ∈ 𝓕 a`, for almost every `t > a`,
--
--     `∫_A G (t, ·) dP = ∫_A E[U (t, ·) | 𝓕 t] dP`.
--
--   This is the pointwise `E[Uₜ | 𝓕ₜ]` content of the product-`L²` projection: only the uniformity
--   of the exceptional times over the generating events is left open.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L301-L319
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L301-L319

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

theorem Malliavin.exists_representative_predictableProjection (U : TimeProcessL2 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      (∀ t, StronglyMeasurable[𝓕 t] fun ω ↦ G (t, ω)) ∧
      ∀ (a : ℝ≥0) (A : Set W), MeasurableSet[𝓕 a] A →
        ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
          ∫ ω in A, G (t, ω) ∂P
            = ∫ ω in A, (P[(fun ω ↦ U (t, ω)) | 𝓕 t]) ω ∂P := by sorry

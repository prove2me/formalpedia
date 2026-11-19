-- Prove2me | Theorems.Thm_InnerProductSpace_volume_closedBall_div_u0027__p2m_00b40815a546
-- name    : InnerProductSpace.volume_closedBall_div_u0027__p2m_00b40815a546
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T22:11:46.77229+00:00
-- url     : https://prove2.me/theorems/8df154b9-b4fb-45ee-9cb8-0419a2ccc8a0
-- title:
--   volume closedBall div'
-- statement:
--   The source theorem `InnerProductSpace.volume_closedBall_div'` is extracted from `BrownianMotion.Auxiliary.MeasureTheory`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F000


/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

@[expose] public section

open MeasureTheory WithLp

open scoped ENNReal NNReal ProbabilityTheory

                                     

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)}

variable [∀ i, IsProbabilityMeasure (μ i)]

end iIndepFun

section covariance

end covariance

end ProbabilityTheory

--generalizing `MeasureTheory.Measure.addHaar_ball_center`

open Metric

theorem InnerProductSpace.volume_closedBall_div_u0027__p2m_00b40815a546 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x y : E) (r s : ℝ≥0∞) :
    volume (Metric.closedEBall x r) / volume (Metric.closedEBall y s) =
      (r / s) ^ (Module.finrank ℝ E) := by sorry

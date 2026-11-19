-- Prove2me | Theorems.Thm_IndepSets_setIntegral_eq_mul
-- name    : IndepSets.setIntegral_eq_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:12:26.09806+00:00
-- url     : https://prove2.me/theorems/4706263b-2aba-490a-ab6e-4625d2b0170e
-- title:
--   setIntegral eq mul
-- statement:
--   The source theorem `IndepSets.setIntegral_eq_mul` is extracted from `BrownianMotion.Auxiliary.MeasureTheory`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F001


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

section covariance

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y Z : Ω → ℝ} (c : ℝ)

end ProbabilityTheory

open ProbabilityTheory MeasurableSpace

theorem IndepSets.setIntegral_eq_mul {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} [IsZeroOrProbabilityMeasure μ]
    {f : 𝓧 → ℝ} {A : Set Ω} (hA1 : IndepSets {A} {s | MeasurableSet[m𝓧.comap X] s} μ)
    (hX : Measurable X) (hA2 : MeasurableSet A)
    (hf : AEStronglyMeasurable f (μ.map X)) :
    ∫ ω in A, f (X ω) ∂μ = μ.real A * ∫ ω, f (X ω) ∂μ := by sorry

-- Prove2me | Theorems.Thm_OAI_Rokhlin_MeasurablePolarRectangle_torus_coordinates
-- name    : OAI.Rokhlin.MeasurablePolarRectangle.torus_coordinates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:47:41.400916+00:00
-- url     : https://prove2.me/theorems/04d17302-d6be-44e3-a8fa-18fc085485e5
-- title:
--   OAI.Rokhlin.MeasurablePolarRectangle.torus_coordinates: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.MeasurablePolarRectangle.torus_coordinates` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin`, with `open MeasureTheory ProbabilityTheory ContinuousLinearMap`):
--
--   ```lean
--   lemma MeasurablePolarRectangle.torus_coordinates
--       (R : MeasurablePolarRectangle μ μX μY μC μD F G K N x y c d)
--       (hR : R.HasHaarNormalization)
--       {z : Ω → Z}
--       (κ : Kernel Z (X × Y)) (ξ : Kernel Z (C × D)) [IsMarkovKernel κ] [IsMarkovKernel ξ]
--       (hκ : HasCondDistrib (fun ω => (x ω,y ω)) z κ μ)
--       (hξ : HasCondDistrib (fun ω => (c ω,d ω)) z ξ μ)
--       (hpair : HasCondDistrib (fun ω => ((x ω,y ω),(c ω,d ω))) z (κ ×ₖ ξ) μ)
--       (hκm : ∀ᵐ v ∂μ.map z, (κ v).map Prod.fst = μX ∧ (κ v).map Prod.snd = μY)
--       (hξm : ∀ᵐ v ∂μ.map z, (ξ v).map Prod.fst = μC ∧ (ξ v).map Prod.snd = μD) :
--       ∃ (J : Type u) (_ : Countable J)
--         (A : X → J → Circle) (B : Y → J → Circle)
--         (P : C → J → Circle) (Q : D → J → Circle) (H : Z → J → Circle),
--         Measurable A ∧ Measurable B ∧ Measurable P ∧ Measurable Q ∧ Measurable H ∧
--         lpMeas ℂ ℂ (MeasurableSpace.comap R.a.unitary inferInstance) 2 μX =
--           lpMeas ℂ ℂ (MeasurableSpace.comap A inferInstance) 2 μX ∧
--         lpMeas ℂ ℂ (MeasurableSpace.comap R.b.unitary inferInstance) 2 μY =
--           lpMeas ℂ ℂ (MeasurableSpace.comap B inferInstance) 2 μY ∧
--         (∀ᵐ ω ∂μ, H (z ω) = A (x ω) * (B (y ω))⁻¹) ∧
--         (∀ᵐ ω ∂μ, H (z ω) = P (c ω) * (Q (d ω))⁻¹)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.MeasurablePolarRectangle`, `OAI.Rokhlin.MeasurablePolar` and `OAI.Rokhlin.StrongUnitary.measurableSpace` (definitions bundle `OAIQ3Ro000` of this split); `OAI.Rokhlin.instMeasurableSpaceCircle_solutions` (definitions bundle `OAIQ3Ro001` of this split); `OAI.Rokhlin.MeasurablePolarRectangle.HasHaarNormalization` (definitions bundle `OAIQ3Ro002` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean (declaration OAI.Rokhlin.MeasurablePolarRectangle.torus_coordinates)

import Mathlib
import Definitions.Def_OAIQ3Ro002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
universe u
variable {Ω Z X Y C D H₁ H₂ H₃ : Type*} {H₄ : Type u}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_solutions
omit [SecondCountableTopology H₁] [IsProbabilityMeasure μY] [IsProbabilityMeasure μD] in

lemma MeasurablePolarRectangle.torus_coordinates
    (R : MeasurablePolarRectangle μ μX μY μC μD F G K N x y c d)
    (hR : R.HasHaarNormalization)
    {z : Ω → Z}
    (κ : Kernel Z (X × Y)) (ξ : Kernel Z (C × D)) [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) z κ μ)
    (hξ : HasCondDistrib (fun ω => (c ω,d ω)) z ξ μ)
    (hpair : HasCondDistrib (fun ω => ((x ω,y ω),(c ω,d ω))) z (κ ×ₖ ξ) μ)
    (hκm : ∀ᵐ v ∂μ.map z, (κ v).map Prod.fst = μX ∧ (κ v).map Prod.snd = μY)
    (hξm : ∀ᵐ v ∂μ.map z, (ξ v).map Prod.fst = μC ∧ (ξ v).map Prod.snd = μD) :
    ∃ (J : Type u) (_ : Countable J)
      (A : X → J → Circle) (B : Y → J → Circle)
      (P : C → J → Circle) (Q : D → J → Circle) (H : Z → J → Circle),
      Measurable A ∧ Measurable B ∧ Measurable P ∧ Measurable Q ∧ Measurable H ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap R.a.unitary inferInstance) 2 μX =
        lpMeas ℂ ℂ (MeasurableSpace.comap A inferInstance) 2 μX ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap R.b.unitary inferInstance) 2 μY =
        lpMeas ℂ ℂ (MeasurableSpace.comap B inferInstance) 2 μY ∧
      (∀ᵐ ω ∂μ, H (z ω) = A (x ω) * (B (y ω))⁻¹) ∧
      (∀ᵐ ω ∂μ, H (z ω) = P (c ω) * (Q (d ω))⁻¹) := by
  sorry
end

end Rokhlin

end

end OAI
end

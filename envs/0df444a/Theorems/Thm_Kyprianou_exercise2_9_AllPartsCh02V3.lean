-- Prove2me | Theorems.Thm_Kyprianou_exercise2_9_AllPartsCh02V3
-- name    : Kyprianou.exercise2_9_AllPartsCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:27:39.904085+00:00
-- url     : https://prove2.me/theorems/1ee53838-1258-472d-b7f4-900cc414ab5e
-- title:
--   Exercise 2.9: variance-gamma Brownian time change and two-gamma decomposition
-- statement:
--   Both parts: subordinate drifted Brownian motion with an independent gamma clock to obtain the variance-gamma characteristic exponent, then establish equality in law with a difference of two independent gamma subordinators with the explicit source rate parameters.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.9, pp. 62-66; see source-issues.json for transcription corrections

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem exercise2_9_AllPartsCh02V3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (α β c σ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hσ : 0 < σ)
    (Γ : ℝ≥0 → Ω → ℝ≥0)
    (hΓlevy : ProbabilityTheory.IsLevyProcess
      (fun t ω => (Γ t ω : ℝ)) P)
    (hΓsub : ∀ᵐ ω ∂P, Monotone (fun t => Γ t ω))
    (hΓlaplace : ∀ (q : ℝ), 0 ≤ q → ∀ (t : ℝ≥0),
      ∫ ω, Real.exp (-q * (Γ t ω : ℝ)) ∂P =
        Real.exp (-(t : ℝ) * β * Real.log (1 + q / α)))
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then B.W (t : ℝ) ω else (Γ t ω : ℝ)) P) :
    let X : ℝ≥0 → Ω → ℝ := fun t ω =>
      c * (Γ t ω : ℝ) + σ * B.W (Γ t ω : ℝ) ω
    let αpos : ℝ :=
      (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α))
        + c / (2 * α))⁻¹
    let αneg : ℝ :=
      (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α))
        - c / (2 * α))⁻¹
    (ProbabilityTheory.IsLevyProcess X P ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (X t)) ξ =
        Complex.exp (-(((t : ℝ) : ℂ)) * (β : ℂ) *
          Complex.log (1 - Complex.I *
            (((ξ * c / α : ℝ) : ℂ)) +
            (((σ ^ 2 * ξ ^ 2 / (2 * α) : ℝ) : ℂ)))) ∧
    (∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
      letI : MeasurableSpace Ω' := measΩ'
      ∃ (P' : Measure Ω') (probP' : IsProbabilityMeasure P'),
        letI : IsProbabilityMeasure P' := probP'
        ∃ (Γpos Γneg : ℝ≥0 → Ω' → ℝ≥0),
          ProbabilityTheory.IsLevyProcess
            (fun t ω => (Γpos t ω : ℝ)) P' ∧
          ProbabilityTheory.IsLevyProcess
            (fun t ω => (Γneg t ω : ℝ)) P' ∧
          (∀ᵐ ω ∂P', Monotone (fun t => Γpos t ω)) ∧
          (∀ᵐ ω ∂P', Monotone (fun t => Γneg t ω)) ∧
          ProbabilityTheory.iIndepFun
            (fun (i : Fin 2) (ω : Ω') => fun t : ℝ≥0 =>
              if i = 0 then (Γpos t ω : ℝ) else (Γneg t ω : ℝ)) P' ∧
          (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
            ∫ ω, Real.exp (-q * (Γpos t ω : ℝ)) ∂P' =
              Real.exp (-(t : ℝ) * β *
                Real.log (1 + q / αpos))) ∧
          (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
            ∫ ω, Real.exp (-q * (Γneg t ω : ℝ)) ∂P' =
              Real.exp (-(t : ℝ) * β *
                Real.log (1 + q / αneg))) ∧
          (∀ t : ℝ≥0, ∀ ξ : ℝ,
            charFun (P.map (X t)) ξ =
            charFun (P'.map (fun ω =>
              (Γpos t ω : ℝ) - (Γneg t ω : ℝ))) ξ)))
      := by sorry
end Kyprianou

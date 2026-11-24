-- Prove2me | Theorems.Thm_Kyprianou_exercise2_12_AllPartsCh02V4
-- name    : Kyprianou.exercise2_12_AllPartsCh02V4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T16:35:19.92407+00:00
-- url     : https://prove2.me/theorems/b89f607d-e596-4e56-a77f-f81a56320304
-- title:
--   Exercise 2.12: four examples of Brownian subordination and stable index qualification [corrected representative]
-- statement:
--   All four parts: Brownian subordinated by stable alpha/2; symmetric-exponential compound Poisson as sqrt(2) Brownian subordinated by a specified jump clock; Gaussian-jump compound Poisson as Brownian sampled at a Poisson clock; and a symmetric alpha-stable process represented in law by stable alpha/beta subordinated by beta. Corrected necessary condition alpha/beta<=2; the printed solutions omit part (iv). Corrected: pointwise-zero Brownian normalisation
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.12, pp. 62-66; see source-issues.json for transcription corrections; representative/measurability correction, 2026-11-16

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem exercise2_12_AllPartsCh02V4 :
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P]
       (α C : ℝ) (hα : 0 < α) (hα2 : α < 2) (hC : 0 < C)
       (B : LevyStochCalc.Brownian.BrownianMotion P)
       (τ : ℝ≥0 → Ω → ℝ≥0)
       (hτ : ProbabilityTheory.IsLevyProcess
         (fun t ω => (τ t ω : ℝ)) P)
       (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
       (hlaplace : ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
         ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P =
         Real.exp (-(t : ℝ) * C * q ^ (α / 2)))
       (hind : ProbabilityTheory.iIndepFun
         (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then B.W (t : ℝ) ω else (τ t ω : ℝ)) P),
       ProbabilityTheory.IsLevyProcess
         (fun t ω => (B.W (τ t ω : ℝ) ω - B.W 0 ω)) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map (fun ω => (B.W (τ t ω : ℝ) ω - B.W 0 ω))) ξ =
         Complex.exp ((-(t : ℝ) * C * ((ξ ^ 2 / 2) ^ (α / 2)) : ℝ))) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P] (a : ℝ) (ha : 0 < a)
       (B : LevyStochCalc.Brownian.BrownianMotion P)
       (τ : ℝ≥0 → Ω → ℝ≥0)
       (hτ : ProbabilityTheory.IsLevyProcess
         (fun t ω => (τ t ω : ℝ)) P)
       (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
       (hlaplace : ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
         ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P =
         Real.exp (-(t : ℝ) * (2 / a) * (q / (q + a ^ 2))))
       (hind : ProbabilityTheory.iIndepFun
         (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then B.W (t : ℝ) ω else (τ t ω : ℝ)) P),
       ProbabilityTheory.IsLevyProcess
         (fun t ω => Real.sqrt 2 * (B.W (τ t ω : ℝ) ω - B.W 0 ω)) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map
           (fun ω => Real.sqrt 2 * (B.W (τ t ω : ℝ) ω - B.W 0 ω))) ξ =
         Complex.exp ((-(t : ℝ) * (2 / a) *
           (ξ ^ 2 / (ξ ^ 2 + a ^ 2)) : ℝ))) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P] (rate σ : ℝ)
       (hrate : 0 < rate) (hσ : 0 < σ)
       (B : LevyStochCalc.Brownian.BrownianMotion P)
       (N : ℝ≥0 → Ω → ℕ)
       (hNlaw : ∀ t : ℝ≥0,
         P.map (N t) =
         ProbabilityTheory.poissonMeasure (⟨2 * rate * (t : ℝ), by positivity⟩))
       (hNlevy : ProbabilityTheory.IsLevyProcess
         (fun t ω => (N t ω : ℝ)) P)
       (hind : ProbabilityTheory.iIndepFun
         (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then B.W (t : ℝ) ω else (N t ω : ℝ)) P),
       ProbabilityTheory.IsLevyProcess
         (fun t ω => σ * (B.W (N t ω : ℝ) ω - B.W 0 ω)) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map
           (fun ω => σ * (B.W (N t ω : ℝ) ω - B.W 0 ω))) ξ =
         Complex.exp ((-(t : ℝ) * 2 * rate *
           (1 - Real.exp (-(σ ^ 2 * ξ ^ 2) / 2)) : ℝ))) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P]
       (α β C : ℝ) (hα : 0 < α) (hα2 : α < 2)
       (hβ : 0 < β) (hβ1 : β < 1)
       (hadmissible : α / β ≤ 2) (hC : 0 < C)
       (X : ℝ≥0 → Ω → ℝ)
       (hX : ProbabilityTheory.IsLevyProcess X P)
       (hXstable : ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map (X t)) ξ =
         Complex.exp ((-(t : ℝ) * C * |ξ| ^ α : ℝ))),
       ∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
         letI : MeasurableSpace Ω' := measΩ'
         ∃ (P' : Measure Ω') (probP' : IsProbabilityMeasure P'),
           letI : IsProbabilityMeasure P' := probP'
           ∃ (Y : ℝ≥0 → Ω' → ℝ) (τ : ℝ≥0 → Ω' → ℝ≥0),
             ProbabilityTheory.IsLevyProcess Y P' ∧
             ProbabilityTheory.IsLevyProcess
               (fun t ω => (τ t ω : ℝ)) P' ∧
             (∀ᵐ ω ∂P', Monotone (fun t => τ t ω)) ∧
             (∀ (t : ℝ≥0) (ξ : ℝ),
               charFun (P'.map (Y t)) ξ =
               Complex.exp ((-(t : ℝ) *
                 (C ^ (1 / β)) * |ξ| ^ (α / β) : ℝ))) ∧
             (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
               ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P' =
               Real.exp (-(t : ℝ) * q ^ β)) ∧
             ProbabilityTheory.iIndepFun
               (fun (i : Fin 2) (ω : Ω') => fun t : ℝ≥0 =>
                 if i = 0 then Y t ω else (τ t ω : ℝ)) P' ∧
             ProbabilityTheory.IsLevyProcess
               (fun t ω => Y (τ t ω) ω) P' ∧
             (∀ (t : ℝ≥0),
               P.map (X t) =
                 P'.map (fun ω => Y (τ t ω) ω)))
      := by sorry
end Kyprianou

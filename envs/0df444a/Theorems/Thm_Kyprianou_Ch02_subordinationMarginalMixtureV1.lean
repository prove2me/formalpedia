-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinationMarginalMixtureV1
-- name    : Kyprianou.Ch02.subordinationMarginalMixtureV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:32:21.285275+00:00
-- url     : https://prove2.me/theorems/35573706-9f3f-4bbc-a671-fb0d262f95dc
-- title:
--   subordinationMarginalMixture
-- statement:
--   subordinationMarginalMixture
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinationMarginalMixtureV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (Ψ : ℝ → ℂ)
    (hψ : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ = Complex.exp (-(((t : ℝ) : ℂ)) * Ψ ξ)) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
        ∫ ω, Complex.exp (-(((τ t ω : ℝ) : ℂ)) * Ψ ξ) ∂P := by sorry

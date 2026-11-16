-- Prove2me | Theorems.Thm_Kyprianou_independentSubordinationCh02V3
-- name    : Kyprianou.independentSubordinationCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:28:49.17621+00:00
-- url     : https://prove2.me/theorems/e130d710-bd7b-4bb5-bc8a-8cbe8de6376d
-- title:
--   Lemma 2.15: independent subordination and complex exponent composition
-- statement:
--   For any real Lévy process X with exponent Psi and an independent nondecreasing Lévy process tau with its Lévy-Khintchine triple, the time-changed process X(tau_t) is again a Lévy process. Its exponent is Xi(Psi(theta)), where Xi is the actual complex half-plane Laplace exponent derived from the drift and Lévy measure of tau. The complex Laplace transform identity is a conclusion to establish, not an additional assumed hypothesis.
-- source:
--   A. E. Kyprianou (2006), Lemma 2.15 and proof of (2.27), p. 61; correction removes unsupported complex-Laplace hypothesis

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem independentSubordinationCh02V3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (Ψ : ℝ → ℂ)
    (aτ : ℝ) (στ : ℝ≥0) (ντ : Measure ℝ)
    (hντ : ProbabilityTheory.IsLevyMeasure ντ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess
       (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (hψ : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ψ ξ))
    (hτchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => (τ t ω : ℝ))) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-aτ, στ ^ 2, ντ, hντ⟩ ξ)) :
    let d : ℝ := -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ
    let Ξ : ℂ → ℂ := fun z =>
      (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ),
        (1 - Complex.exp (-z * ((x : ℝ) : ℂ))) ∂ντ
    ProbabilityTheory.IsLevyProcess
      (fun t ω => X (τ t ω) ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
      Complex.exp (-(((t : ℝ) : ℂ)) * Ξ (Ψ ξ)) := by sorry

end Kyprianou

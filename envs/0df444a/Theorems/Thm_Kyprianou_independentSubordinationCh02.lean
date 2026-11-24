-- Prove2me | Theorems.Thm_Kyprianou_independentSubordinationCh02
-- name    : Kyprianou.independentSubordinationCh02
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:22:30.713569+00:00
-- url     : https://prove2.me/theorems/09040374-f146-471c-a1b4-4872b1ae22a4
-- title:
--   Lemma 2.15: independent subordination preserves the Lévy property
-- statement:
--   Lemma 2.15: independent subordination preserves the Lévy property. Independent Lévy process time-changed by a subordinator, with exponent composition.
-- source:
--   A. E. Kyprianou (2006), Chapter 2, pp. 33–66

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem independentSubordinationCh02
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (Ψ : ℝ → ℂ) (Ξ : ℂ → ℂ)
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
    (hξ : ∀ (t : ℝ≥0) (z : ℂ), 0 ≤ z.re →
      ∫ ω, Complex.exp (-z * (((τ t ω : ℝ) : ℂ))) ∂P =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z)) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => X (τ t ω) ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
      Complex.exp (-(((t : ℝ) : ℂ)) * Ξ (Ψ ξ)) := by sorry

end Kyprianou

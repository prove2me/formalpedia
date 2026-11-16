-- Prove2me | Theorems.Thm_Kyprianou_exercise2_8_AllPartsCh02V3
-- name    : Kyprianou.exercise2_8_AllPartsCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:24:45.602288+00:00
-- url     : https://prove2.me/theorems/e7c9d65a-022d-490f-b2fd-325344d78c9f
-- title:
--   Exercise 2.8: bounded variation as a difference of independent subordinators
-- statement:
--   A bounded-variation Lévy process is a difference of two independent subordinators, decomposing positive and negative jumps and the positive and negative parts of its finite-variation drift.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.8, pp. 62-66; author solutions pp. 307-311; corrections recorded where needed

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem exercise2_8_AllPartsCh02V3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    ∃ (Spos Sneg : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess Spos P ∧
      ProbabilityTheory.IsLevyProcess Sneg P ∧
      (∀ᵐ ω ∂P, Monotone (fun t => Spos t ω)) ∧
      (∀ᵐ ω ∂P, Monotone (fun t => Sneg t ω)) ∧
      ProbabilityTheory.iIndepFun
        (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then Spos t ω else Sneg t ω) P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = Spos t ω - Sneg t ω)
      := by sorry

end Kyprianou

-- Prove2me | Theorems.Thm_Kyprianou_exercise2_2_AllPartsCh02V3
-- name    : Kyprianou.exercise2_2_AllPartsCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:25:52.908429+00:00
-- url     : https://prove2.me/theorems/3d7b0a16-e692-4a13-bffd-b8455d42e95f
-- title:
--   Exercise 2.2: Poisson arrival order statistics and ordered uniform samples
-- statement:
--   Part (i) gives the joint conditional law of the first n Poisson arrivals given N_t=n, with density n!/t^n on the ordered simplex. Part (ii) identifies that conditional law with sorted independent uniform observations on [0,t]. The actual process has Poisson marginals, Lévy independent increments, and arrival times defined by its counting process.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.2, pp. 62-66; corrections tracked in source-issues.json

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem exercise2_2_AllPartsCh02V3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (hrate : 0 < rate)
    (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (hNlaw : ∀ t, P.map (N t) =
      ProbabilityTheory.poissonMeasure (rate * t))
    (hNlevy : ProbabilityTheory.IsLevyProcess
      (fun t ω => (N t ω : ℝ)) P)
    (harrival : ∀ᵐ ω ∂P, ∀ (n : ℕ), 0 < n →
      ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t)) :
    (∀ (t : ℝ≥0), 0 < t → ∀ (n : ℕ), 0 < n →
      ∀ (A : Set (Fin n → ℝ)), MeasurableSet A →
        P {ω | N t ω = n ∧
          (fun i : Fin n => ((T (i.val + 1) ω : ℝ))) ∈ A} =
        P {ω | N t ω = n} *
          ENNReal.ofReal ((Nat.factorial n : ℝ) / ((t : ℝ) ^ n)) *
          volume (A ∩
            {v : Fin n → ℝ |
              (∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)) ∧
              Monotone v})) ∧
    (∀ (t : ℝ≥0), 0 < t → ∀ (n : ℕ), 0 < n →
      ∀ (U V : Fin n → Ω → ℝ),
        (∀ i, P.map (U i) =
          (ENNReal.ofReal (t : ℝ))⁻¹ •
            (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)))) →
        ProbabilityTheory.iIndepFun U P →
        (∀ᵐ ω ∂P,
          Monotone (fun i : Fin n => V i ω) ∧
          (List.ofFn (fun i : Fin n => V i ω)).Perm
            (List.ofFn (fun i : Fin n => U i ω))) →
        ((P.restrict {ω | N t ω = n}).map
          (fun ω => fun i : Fin n => (T (i.val + 1) ω : ℝ))) =
        (P {ω | N t ω = n}) •
          (P.map (fun ω => fun i : Fin n => V i ω)))
      := by sorry
end Kyprianou

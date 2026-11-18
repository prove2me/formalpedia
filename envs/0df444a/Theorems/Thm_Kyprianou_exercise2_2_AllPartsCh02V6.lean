-- Prove2me | Theorems.Thm_Kyprianou_exercise2_2_AllPartsCh02V6
-- name    : Kyprianou.exercise2_2_AllPartsCh02V6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T12:47:08.399289+00:00
-- url     : https://prove2.me/theorems/899ebb54-47cf-4367-bcec-20844d616891
-- title:
--   Exercise 2.2: Poisson arrival order statistics and ordered uniform samples [corrected representative] [positive arrival indices]
-- statement:
--   Part (i) gives the joint conditional law of the first n Poisson arrivals given N_t=n, with density n!/t^n on the ordered simplex. Part (ii) identifies that conditional law with sorted independent uniform observations on [0,t]. The actual process has Poisson marginals, Lévy independent increments, and arrival times defined by its counting process. Corrected: explicit measurable arrival/mark evaluation in non-complete spaces V6 source-faithful correction: Poisson arrival times T_n exist only for n>0. The redundant measurability of unconstrained T_0 is no longer required.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.2, pp. 62-66; corrections tracked in source-issues.json; representative/measurability correction, 2026-11-16; original Chapter 2 source-scope repair, 17 November 2026

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem exercise2_2_AllPartsCh02V6
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (hrate : 0 < rate)
    (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
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

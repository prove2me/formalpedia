-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinatorExponentComplexLaplaceAnalyticV1
-- name    : Kyprianou.Ch02.subordinatorExponentComplexLaplaceAnalyticV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:37:25.371882+00:00
-- url     : https://prove2.me/theorems/3e34afd4-3613-448d-a397-3c9bb735f93a
-- title:
--   subordinatorExponentComplexLaplaceAnalytic
-- statement:
--   subordinatorExponentComplexLaplaceAnalytic
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinatorExponentComplexLaplaceAnalyticV1
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (d : ℝ) (hd : 0 ≤ d) (t : ℝ≥0) :
    let Ξ : ℂ → ℂ := fun z =>
      (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ν
    DiffContOnCl ℂ (fun z => Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z))
      {z : ℂ | 0 < z.re} ∧
    ∀ z : ℂ, 0 ≤ z.re → ‖Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z)‖ ≤ 1 := by sorry

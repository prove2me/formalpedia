-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinatorComplexLaplaceImaginaryBoundaryV1
-- name    : Kyprianou.Ch02.subordinatorComplexLaplaceImaginaryBoundaryV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:37:31.579069+00:00
-- url     : https://prove2.me/theorems/b76d8b25-0220-41fd-b18a-aca15a45c701
-- title:
--   subordinatorComplexLaplaceImaginaryBoundary
-- statement:
--   subordinatorComplexLaplaceImaginaryBoundary
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinatorComplexLaplaceImaginaryBoundaryV1
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) (d : ℝ) (t : ℝ≥0)
    (hchar : ∀ ξ : ℝ, charFun Q ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        (Complex.I * ((d * ξ : ℝ) : ℂ) +
          ∫ x in Set.Ioi (0 : ℝ),
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν))) :
    let Ξ : ℂ → ℂ := fun z => (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ν
    ∀ y : ℝ, (∫ x, Complex.exp (-((y : ℂ) * Complex.I) * (x : ℂ)) ∂Q) =
      Complex.exp (-(((t : ℝ) : ℂ)) * Ξ ((y : ℂ) * Complex.I)) := by sorry

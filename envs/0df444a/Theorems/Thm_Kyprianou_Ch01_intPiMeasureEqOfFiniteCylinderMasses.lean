-- Prove2me | Theorems.Thm_Kyprianou_Ch01_intPiMeasureEqOfFiniteCylinderMasses
-- name    : Kyprianou.Ch01.intPiMeasureEqOfFiniteCylinderMasses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:18:07.803193+00:00
-- url     : https://prove2.me/theorems/5662ff07-456a-40d8-a0d5-c5893ae9a673
-- title:
--   Finite cylinder masses determine integer-valued path measures
-- statement:
--   For finite integer-valued product measures, equality of all finite measurable rectangle masses implies equality of the entire path-space measures. An exact type adaptation of the already-Proved real-valued Avram theorem UUID 4d62c918-6680-4aa9-98a1-d28e432ce446, requiring an independently verified proof.
-- source:
--   MeasureTheory uniqueness under pi-system generation, as instantiated in AvramDividend.Classical.piPathMeasure_eq_of_finite_cylinder_masses, pinned Mathlib.

import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.IdentDistrib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.intPiMeasureEqOfFiniteCylinderMasses
    {ι : Type*} (μ ν : Measure (ι → ℤ))
    (hFinite : μ Set.univ ≠ ⊤)
    (hCyl : ∀ (J : Finset ι) (B : ι → Set ℤ),
      (∀ i ∈ J, MeasurableSet (B i)) →
      μ (Set.pi (J : Set ι) B) = ν (Set.pi (J : Set ι) B)) :
    μ = ν := by
  sorry

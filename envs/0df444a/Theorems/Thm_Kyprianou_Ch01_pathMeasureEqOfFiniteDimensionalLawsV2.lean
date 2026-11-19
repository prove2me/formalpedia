-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pathMeasureEqOfFiniteDimensionalLawsV2
-- name    : Kyprianou.Ch01.pathMeasureEqOfFiniteDimensionalLawsV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:47:57.921426+00:00
-- url     : https://prove2.me/theorems/f48b4066-d10f-4607-82cc-a6aa66cfaec7
-- title:
--   Measurable path-space laws are determined by their finite-dimensional distributions
-- statement:
--   Uniqueness of probability measure on the product sigma-algebra of integer-valued NNReal-indexed paths from equality of all finite-dimensional coordinate pushforwards, assuming the two random path maps are measurable. It is the standard cylinder-set uniqueness step in stochastic process theory.
-- source:
--   Kolmogorov cylinder uniqueness theorem; Kyprianou (2006), Chapter 1, §1.3.4.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.pathMeasureEqOfFiniteDimensionalLawsV2
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (F : Ω → (ℝ≥0 → ℤ)) (G : Ω' → (ℝ≥0 → ℤ))
    (hF : Measurable F) (hG : Measurable G)
    (hJoint : ∀ n : ℕ, ∀ times : Fin n → ℝ≥0,
      P.map (fun ω => fun i : Fin n => F ω (times i)) =
      Q.map (fun ω => fun i : Fin n => G ω (times i))) :
    P.map F = Q.map G := by
  sorry

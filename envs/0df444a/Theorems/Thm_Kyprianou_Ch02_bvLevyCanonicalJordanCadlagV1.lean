-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanCadlagV1
-- name    : Kyprianou.Ch02.bvLevyCanonicalJordanCadlagV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:20:36.890471+00:00
-- url     : https://prove2.me/theorems/42d23808-c6a6-4055-a909-c0a46f3f480f
-- title:
--   Canonical Jordan variations have càdlàg paths
-- statement:
--   The signed variation has right limit given by variationOnFromTo.tendsto_right and left limit by variationOnFromTo.tendsto_left. Right continuity of the original path makes the right-limit correction zero. Addition, subtraction and division by two preserve these limits.
-- source:
--   Kyprianou (2006), Exercise 2.8; canonical Jordan variation increments.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyCanonicalJordanCadlagV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    (∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag (fun t => Spos t ω)) ∧
    (∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag (fun t => Sneg t ω)) := by sorry

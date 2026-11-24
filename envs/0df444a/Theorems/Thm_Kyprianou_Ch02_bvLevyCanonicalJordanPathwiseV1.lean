-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPathwiseV1
-- name    : Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:15:12.153749+00:00
-- url     : https://prove2.me/theorems/e34795de-0085-4e61-9512-e7b85b848a55
-- title:
--   Canonical Jordan variation processes are monotone and recover the path
-- statement:
--   Apply the deterministic Mathlib monotonicity of variation plus and minus the original bounded-variation function; division by two preserves monotonicity. The difference identity is algebraic.
-- source:
--   Kyprianou (2006), Exercise 2.8. Canonical Jordan variation route via fine deterministic partitions, alternative to drift plus raw jump sums.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    (∀ᵐ ω ∂P, Monotone (fun t => Spos t ω)) ∧
    (∀ᵐ ω ∂P, Monotone (fun t => Sneg t ω)) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = Spos t ω - Sneg t ω) := by sorry

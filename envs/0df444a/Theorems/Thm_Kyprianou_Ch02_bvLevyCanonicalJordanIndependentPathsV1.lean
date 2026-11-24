-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanIndependentPathsV1
-- name    : Kyprianou.Ch02.bvLevyCanonicalJordanIndependentPathsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:15:13.201807+00:00
-- url     : https://prove2.me/theorems/702937b0-c717-47fb-a071-c9ef61319e51
-- title:
--   Canonical positive and negative variations are independent as whole paths
-- statement:
--   For each finite partition, subdivide each interval into n equal cells. For a cell increment Z the two nonnegative increments Z⁺ and Z⁻ have disjoint positive supports, hence E exp(-u Z⁺-v Z⁻)=1-a_n-b_n. Positive and negative variation sums converge on refining grids. Their finite limits imply n a_n and n b_n are bounded, using (1-a_n)^n and (1-b_n)^n bounded away from zero. Thus (1-a_n-b_n)^n and (1-a_n)^n(1-b_n)^n have the same limit, since their difference is bounded by n a_n b_n. Across disjoint time blocks, independence of original increments gives the product of these factors. Uniqueness of multivariate Laplace transforms on the nonnegative orthant and finite-cylinder independence establish independence of both whole paths.
-- source:
--   Kyprianou (2006), Exercise 2.8. Canonical Jordan variation route via fine deterministic partitions, alternative to drift plus raw jump sums.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyCanonicalJordanIndependentPathsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then Spos t ω else Sneg t ω) P := by sorry

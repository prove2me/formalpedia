-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_exponent_unbounded
-- name    : Kyprianou.Ch08.StageB.source_result81_levy_exponent_unbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:32:02.278371+00:00
-- url     : https://prove2.me/theorems/91df3efd-1ae5-43dd-bbea-1dc16193d582
-- title:
--   Unbounded Laplace exponent from a positive marginal
-- statement:
--   If some time marginal charges the positive half-line, the exponential moment lower bound on a positive threshold event forces the Laplace exponent above any prescribed level.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, tilted descending potential. Mathematical reduction of 88aa77e2-4924-42e7-a415-7fcbc4e8ae14.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_levy_exponent_unbounded
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    {t : ℝ≥0} (ht : ¬ (∀ᵐ ω ∂P, A.X t ω ≤ 0)) (q : ℝ) :
    ∃ b : ℝ, 0 < b ∧ q < A.ψ b := by
  sorry

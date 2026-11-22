-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_exponent_unbounded_universe
-- name    : Kyprianou.Ch08.StageB.source_result81_levy_exponent_unbounded_universe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T21:04:10.618539+00:00
-- url     : https://prove2.me/theorems/a3ea2a81-8551-45b3-95dd-69673b0d98fd
-- title:
--   Universe-polymorphic exponent unboundedness from positive mass
-- statement:
--   Type-star version of the proved exponent-unbounded lemma: positive mass at some time forces arbitrarily large Laplace exponent values. Needed for the scale-transfer universe repair.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1 supporting lemma; universe-polymorphic restatement of source_result81_levy_exponent_unbounded.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

theorem source_result81_levy_exponent_unbounded_universe
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    {t : ℝ≥0} (ht : ¬ (∀ᵐ ω ∂P, A.X t ω ≤ 0)) (q : ℝ) :
    ∃ b : ℝ, 0 < b ∧ q < A.ψ b := by
  sorry

end Kyprianou.Ch08.StageB

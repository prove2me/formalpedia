-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_killed_density_bounded_integral_limit
-- name    : Kyprianou.Ch08.StageB.p2m88_killed_density_bounded_integral_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:41:42.795243+00:00
-- url     : https://prove2.me/theorems/35c61e4c-92d0-4e59-b984-08cc16006e30
-- title:
--   Dominated convergence of the half-line density on bounded measurable sets
-- statement:
--   The positive-discount density converges pointwise to the zero-discount density. On a bounded nonnegative set it is dominated by the finite constant W(1,x), so dominated convergence applies.
-- source:
--   Kyprianou (2006), Corollary 8.8, zero-discount limit.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_killed_density_bounded_integral_limit :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ), HasSourceScaleFamily ψ W →
      ∀ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n ≤ 1) → Tendsto r atTop (nhds 0) →
      Tendsto (fun n => Phi ψ (r n)) atTop (nhds (Phi ψ 0)) →
      ∀ x : ℝ, 0 ≤ x → ∀ B : ℝ, 0 ≤ B → ∀ A : Set ℝ, MeasurableSet A →
      A ⊆ Iic B →
      Tendsto (fun n => ((volume.restrict (Ici (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal (killedHalflineDensity ψ (r n) (W (r n)) x y))) A)
        atTop (nhds (((volume.restrict (Ici (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y))) A)) := by
  sorry
end Kyprianou.Ch08.StageB

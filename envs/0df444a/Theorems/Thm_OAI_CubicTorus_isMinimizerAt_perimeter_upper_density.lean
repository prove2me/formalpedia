-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_upper_density
-- name    : OAI.CubicTorus.isMinimizerAt_perimeter_upper_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:08:12.259992+00:00
-- url     : https://prove2.me/theorems/4e143c85-7a39-438e-a620-f44a68fef366
-- title:
--   OAI.CubicTorus.isMinimizerAt_perimeter_upper_density: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_perimeter_upper_density` of [lean/OAI/Geometry/CubicTorus/Estimates/BVRadial.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVRadial.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_perimeter_upper_density {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       ∃ R A : ℝ, 0 < R ∧ 0 < A ∧ ∀ μ : FiniteMeasure NormalBundle,
--         IsNormalMeasure E μ → ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
--           (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) ≤ A * r ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere` and `OAI.CubicTorus.spatialNormalMeasure` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_C1_modulus`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_lipschitz_graph`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_field`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay`, `OAI.CubicTorus.actual_primary_fixed_scale_packets`, `OAI.CubicTorus.actual_primary_offvertex_fixed_graphs`, `OAI.CubicTorus.actual_tangent_secondary_representation`, `OAI.CubicTorus.isMinimizerAt_axialFluxWeight_pos`, `OAI.CubicTorus.isMinimizerAt_axialHeight_absolutelyContinuous`, `OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small`, `OAI.CubicTorus.isMinimizerAt_lipschitz_approximation_with_cones`, `OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy` and `OAI.CubicTorus.isMinimizerAt_paired_blowup` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVRadial.lean (declaration OAI.CubicTorus.isMinimizerAt_perimeter_upper_density)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

theorem isMinimizerAt_perimeter_upper_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R A : ℝ, 0 < R ∧ 0 < A ∧ ∀ μ : FiniteMeasure NormalBundle,
      IsNormalMeasure E μ → ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
        (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) ≤ A * r ^ 2 := by
  sorry

end CubicTorus

end
end

end

end OAI
end

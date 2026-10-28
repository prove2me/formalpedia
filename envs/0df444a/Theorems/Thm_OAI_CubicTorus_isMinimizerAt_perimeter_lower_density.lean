-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_lower_density
-- name    : OAI.CubicTorus.isMinimizerAt_perimeter_lower_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:08:12.657988+00:00
-- url     : https://prove2.me/theorems/bff635ff-3b99-479d-95ac-0662904a5545
-- title:
--   OAI.CubicTorus.isMinimizerAt_perimeter_lower_density: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_perimeter_lower_density` of [lean/OAI/Geometry/CubicTorus/Compactness/BVLocalTranslation.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Compactness/BVLocalTranslation.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_perimeter_lower_density {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ μ : FiniteMeasure NormalBundle,
--         IsNormalMeasure E μ → ∀ a ∈ volumeSupport E ∩ volumeSupport Eᶜ,
--         ∀ r : ℝ, 0 < r → r ≤ R →
--           c * r ^ 2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.spatialNormalMeasure` and `OAI.CubicTorus.volumeSupport` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_lipschitz_graph`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_field`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus`, `OAI.CubicTorus.isMinimizerAt_bottom_both_extents`, `OAI.CubicTorus.isMinimizerAt_bottom_extent_calibration`, `OAI.CubicTorus.isMinimizerAt_centeredJacobiChart`, `OAI.CubicTorus.isMinimizerAt_centered_multiplier`, `OAI.CubicTorus.isMinimizerAt_density_pos`, `OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound`, `OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy`, `OAI.CubicTorus.isMinimizerAt_periodic_ae_eq_boundary`, `OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous` and `OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Compactness/BVLocalTranslation.lean (declaration OAI.CubicTorus.isMinimizerAt_perimeter_lower_density)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

theorem isMinimizerAt_perimeter_lower_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ μ : FiniteMeasure NormalBundle,
      IsNormalMeasure E μ → ∀ a ∈ volumeSupport E ∩ volumeSupport Eᶜ,
      ∀ r : ℝ, 0 < r → r ≤ R →
        c * r ^ 2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) := by
  sorry

end CubicTorus

end
end

end

end OAI
end

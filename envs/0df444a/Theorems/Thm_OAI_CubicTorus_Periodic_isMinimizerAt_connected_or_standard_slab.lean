-- Prove2me | Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_connected_or_standard_slab
-- name    : OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:46:41.906088+00:00
-- url     : https://prove2.me/theorems/d6ba22ae-980a-427f-ba5c-f3db12976d44
-- title:
--   OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab` of [lean/OAI/Geometry/CubicTorus/Estimates/TorusCoordinatePermute.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/TorusCoordinatePermute.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem Periodic.isMinimizerAt_connected_or_standard_slab {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hmin : IsMinimizerAt V E) :
--       IsPreconnected (frontier (openRepresentative E)) ∨
--         (perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.StandardRegionAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.perimeter` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_connected_curvature_integral_pos`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_standard`, `OAI.CubicTorus.isMinimizerAt_fixed_downset_not_three_vertices`, `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux`, `OAI.CubicTorus.isMinimizerAt_small_slab_standard`, `OAI.CubicTorus.isMinimizerAt_standard_or_strict_reflection` and `OAI.CubicTorus.unit_cubic_isoperimetric` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/TorusCoordinatePermute.lean (declaration OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem Periodic.isMinimizerAt_connected_or_standard_slab {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      (perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E) := by
  sorry

end CubicTorus

end
end

end

end OAI
end

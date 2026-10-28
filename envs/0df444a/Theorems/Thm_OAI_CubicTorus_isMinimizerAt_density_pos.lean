-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_density_pos
-- name    : OAI.CubicTorus.isMinimizerAt_density_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:04:20.85398+00:00
-- url     : https://prove2.me/theorems/bd30f2bb-9965-4962-84c7-f2226606fb88
-- title:
--   OAI.CubicTorus.isMinimizerAt_density_pos: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_density_pos` of [lean/OAI/Geometry/CubicTorus/Regularity/BVRadialVariation.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVRadialVariation.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma isMinimizerAt_density_pos {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {a : Torus} (ha : a ∈ frontier (openRepresentative E)) {θ : ℝ}
--       (hθ : Tendsto (fun r : ℝ ↦
--         (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) / r ^ 2)
--         (𝓝[>] 0) (𝓝 θ)) : 0 < θ
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.openRepresentative` and `OAI.CubicTorus.spatialNormalMeasure` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_strict_C1_cone_blowup` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVRadialVariation.lean (declaration OAI.CubicTorus.isMinimizerAt_density_pos)

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

lemma isMinimizerAt_density_pos {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {a : Torus} (ha : a ∈ frontier (openRepresentative E)) {θ : ℝ}
    (hθ : Tendsto (fun r : ℝ ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) / r ^ 2)
      (𝓝[>] 0) (𝓝 θ)) : 0 < θ := by
  sorry

end CubicTorus

end
end

end

end OAI
end

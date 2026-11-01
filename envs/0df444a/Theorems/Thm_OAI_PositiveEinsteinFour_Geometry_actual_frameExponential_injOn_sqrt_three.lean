-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_actual_frameExponential_injOn_sqrt_three
-- name    : OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:49:57.013207+00:00
-- url     : https://prove2.me/theorems/fb8d1392-54b6-43e1-bd91-8da7f892060e
-- title:
--   OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three` of [lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Geometry`, with `open EinsteinFour Set Metric`, `open scoped Manifold ContDiff`):
--
--   ```lean
--   theorem actual_frameExponential_injOn_sqrt_three (g : SmoothMetric M)
--       (o : FrameOrientation g) (hRic : RicciThree g)
--       (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g) (he : e ∈ o.positive) :
--       InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Geometry.RicciThree` (definitions bundle `OAIQ091C008` of this split); `OAI.PositiveEinsteinFour.Geometry.frameExponential` (definitions bundle `OAIQ091C017` of this split); `OAI.EinsteinFour.FourSpace`, `OAI.EinsteinFour.HasPositiveSectionalCurvature`, `OAI.EinsteinFour.I4`, `OAI.EinsteinFour.SmoothMetric`, `OAI.PositiveEinsteinFour.Geometry.FrameBundle` and `OAI.PositiveEinsteinFour.Geometry.FrameOrientation` (the published bundle `Def_EinsteinFour`).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean (declaration OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actual_frameExponential_injOn_sqrt_three (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g) (he : e ∈ o.positive) :
    InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3)) := by
  sorry

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

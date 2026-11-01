-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_actual_derdzinski_hitchin
-- name    : OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:29:24.990437+00:00
-- url     : https://prove2.me/theorems/b37fe5cd-caf6-4fe3-a981-9acf9f6bcea1
-- title:
--   OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin` of [lean/OAI/Geometry/EinsteinFour/ActualModelIdentification.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ActualModelIdentification.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Geometry`, with `open EinsteinFour`, `open scoped Manifold ContDiff`):
--
--   ```lean
--   theorem actual_derdzinski_hitchin (g : SmoothMetric M) (o : FrameOrientation g)
--       (hRic : RicciThree g) : DerdzinskiHitchinInput g o
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Geometry.DerdzinskiHitchinInput` and `OAI.PositiveEinsteinFour.Geometry.RicciThree` (definitions bundle `OAIQ091C008` of this split); `OAI.EinsteinFour.FourSpace`, `OAI.EinsteinFour.I4`, `OAI.EinsteinFour.SmoothMetric` and `OAI.PositiveEinsteinFour.Geometry.FrameOrientation` (the published bundle `Def_EinsteinFour`).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ActualModelIdentification.lean (declaration OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin)

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

namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable [ConnectedSpace M]

omit [CompactSpace M] [SecondCountableTopology M] [ConnectedSpace M] [PreconnectedSpace M] in
theorem actual_derdzinski_hitchin (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : DerdzinskiHitchinInput g o := by
  sorry

end
end PositiveEinsteinFour.Geometry

end OAI
end

-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_coordinate_cylinder_phase
-- name    : OAI.CubicTorus.isMinimizerAt_coordinate_cylinder_phase
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:02:46.229594+00:00
-- url     : https://prove2.me/theorems/3f07e6c4-d5a9-4cc0-96f3-a151f644fa16
-- title:
--   OAI.CubicTorus.isMinimizerAt_coordinate_cylinder_phase: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_coordinate_cylinder_phase` of [lean/OAI/Geometry/CubicTorus/Profiles/TransverseTorus.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/TransverseTorus.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_coordinate_cylinder_phase {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (i : Fin 3) {c : Cover} (hc : sibling_axialProjection (EuclideanSpace.single i 1) c=c)
--       {r : ℝ} (hr0 : 0 ≤ r) (hr : r<1/2)
--       (hbd : frontier (openRepresentative E)=quotientMap '' axialCylinder (EuclideanSpace.single i 1) c r) :
--       E =ᵐ[torusVolume] coordinateTube i (quotientMap c) r ∨
--         E =ᵐ[torusVolume] (coordinateTube i (quotientMap c) r)ᶜ
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.axialCylinder`, `OAI.CubicTorus.coordinateTube`, `OAI.CubicTorus.openRepresentative` and `OAI.CubicTorus.sibling_axialProjection` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/TransverseTorus.lean (declaration OAI.CubicTorus.isMinimizerAt_coordinate_cylinder_phase)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

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

theorem isMinimizerAt_coordinate_cylinder_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) {c : Cover} (hc : sibling_axialProjection (EuclideanSpace.single i 1) c=c)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' axialCylinder (EuclideanSpace.single i 1) c r) :
    E =ᵐ[torusVolume] coordinateTube i (quotientMap c) r ∨
      E =ᵐ[torusVolume] (coordinateTube i (quotientMap c) r)ᶜ := by
  sorry

end CubicTorus

end
end

end

end OAI
end

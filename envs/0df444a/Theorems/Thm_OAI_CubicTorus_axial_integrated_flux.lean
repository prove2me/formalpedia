-- Prove2me | Theorems.Thm_OAI_CubicTorus_axial_integrated_flux
-- name    : OAI.CubicTorus.axial_integrated_flux
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:52:29.442407+00:00
-- url     : https://prove2.me/theorems/a98a8576-55ef-4f77-bb3d-eb4faf699b14
-- title:
--   OAI.CubicTorus.axial_integrated_flux: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.axial_integrated_flux` of [lean/OAI/Geometry/CubicTorus/Profiles/SharpSectionWeight.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SharpSectionWeight.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem axial_integrated_flux {μ : FiniteMeasure NormalBundle} (i : Fin 3)
--       (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
--       Nesting.lambda*axialTransverseMass μ i+
--         (∫ t,Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
--           |axialNormalDensity μ i t|)≤(μ.mass : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.axialAreaMarginal`, `OAI.CubicTorus.axialNormalDensity`, `OAI.CubicTorus.axialPerimeterDensity`, `OAI.CubicTorus.axialSecondDensity`, `OAI.CubicTorus.axialTransverseMass`, `OAI.CubicTorus.Nesting.lambda` and `OAI.CubicTorus.Nesting.weight` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.axial_integrated_flux_actual` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SharpSectionWeight.lean (declaration OAI.CubicTorus.axial_integrated_flux)

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

theorem axial_integrated_flux {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    Nesting.lambda*axialTransverseMass μ i+
      (∫ t,Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
        |axialNormalDensity μ i t|)≤(μ.mass : ℝ) := by
  sorry

end CubicTorus

end
end

end

end OAI
end

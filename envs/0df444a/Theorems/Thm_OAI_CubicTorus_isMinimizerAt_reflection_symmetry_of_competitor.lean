-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_reflection_symmetry_of_competitor
-- name    : OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:35:42.817591+00:00
-- url     : https://prove2.me/theorems/9d6f01d1-410f-46d6-a62f-5fa583bb769b
-- title:
--   OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor` of [lean/OAI/Geometry/CubicTorus/Reflection/NormalMeasureCoordinateReflection.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/NormalMeasureCoordinateReflection.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_reflection_symmetry_of_competitor {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
--       (hconn : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3)
--       (hmF : IsMinimizerAt V (reflectionCompetitor i E (coordinateHalf i 0))) :
--       coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.coordinateHalf`, `OAI.CubicTorus.coordinateReflection` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.reflectionCompetitor` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/NormalMeasureCoordinateReflection.lean (declaration OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_reflection_symmetry_of_competitor {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3)
    (hmF : IsMinimizerAt V (reflectionCompetitor i E (coordinateHalf i 0))) :
    coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E := by
  sorry

end CubicTorus

end
end

end OAI
end

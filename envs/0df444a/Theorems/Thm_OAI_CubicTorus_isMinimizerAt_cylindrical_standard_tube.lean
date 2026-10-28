-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_cylindrical_standard_tube
-- name    : OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:03:27.459286+00:00
-- url     : https://prove2.me/theorems/f987ce14-430f-4d1b-a099-9719b06ea9f5
-- title:
--   OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube` of [lean/OAI/Geometry/CubicTorus/Reflection/TorusCylinders.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/TorusCylinders.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_cylindrical_standard_tube {V : ℝ} (hV : V∈Ioc 0 (1/2))
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (i : Fin 3) {c : Cover} {r : ℝ} (hr0 : 0 < r) (hr : r<1/2)
--       (hbd : frontier (openRepresentative E)=quotientMap '' euclideanCylinder (EuclideanSpace.single i 1) c r) :
--       4*Real.pi/81≤V ∧ V≤1/Real.pi ∧ CongruentAE E (canonicalTube V)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.euclideanCylinder` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.CongruentAE`, `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.canonicalTube` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_nonstandard_section_system` and `OAI.CubicTorus.isMinimizerAt_standard_or_strict_reflection` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/TorusCylinders.lean (declaration OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube)

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

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_cylindrical_standard_tube {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) {c : Cover} {r : ℝ} (hr0 : 0 < r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' euclideanCylinder (EuclideanSpace.single i 1) c r) :
    4*Real.pi/81≤V ∧ V≤1/Real.pi ∧ CongruentAE E (canonicalTube V) := by
  sorry

end CubicTorus

end
end

end OAI
end

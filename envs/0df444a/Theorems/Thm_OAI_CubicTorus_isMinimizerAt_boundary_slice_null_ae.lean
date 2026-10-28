-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_boundary_slice_null_ae
-- name    : OAI.CubicTorus.isMinimizerAt_boundary_slice_null_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:00:33.489641+00:00
-- url     : https://prove2.me/theorems/3a41fc33-d7a9-4d46-bcda-0100daddfb7d
-- title:
--   OAI.CubicTorus.isMinimizerAt_boundary_slice_null_ae: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_boundary_slice_null_ae` of [lean/OAI/Geometry/CubicTorus/Profiles/SmoothSeamProbability.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SmoothSeamProbability.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma isMinimizerAt_boundary_slice_null_ae {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) (i : Fin 3) :
--       ∀ᵐ t : AxisCircle,volume (axialSlice (frontier (openRepresentative E)) i t)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.TransverseProduct`, `OAI.CubicTorus.axialSlice` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_nesting_improved_profile_circle` and `OAI.CubicTorus.isMinimizerAt_planar_profile_circle` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SmoothSeamProbability.lean (declaration OAI.CubicTorus.isMinimizerAt_boundary_slice_null_ae)

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

lemma isMinimizerAt_boundary_slice_null_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) (i : Fin 3) :
    ∀ᵐ t : AxisCircle,volume (axialSlice (frontier (openRepresentative E)) i t)=0 := by
  sorry

end CubicTorus

end
end

end

end OAI
end

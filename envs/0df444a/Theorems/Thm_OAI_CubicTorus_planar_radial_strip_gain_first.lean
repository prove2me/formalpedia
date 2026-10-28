-- Prove2me | Theorems.Thm_OAI_CubicTorus_planar_radial_strip_gain_first
-- name    : OAI.CubicTorus.planar_radial_strip_gain_first
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:20:42.801243+00:00
-- url     : https://prove2.me/theorems/40df9205-d03d-4490-8cd5-4938d3cbf6d7
-- title:
--   OAI.CubicTorus.planar_radial_strip_gain_first: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.planar_radial_strip_gain_first` of [lean/OAI/Geometry/CubicTorus/Profiles/SmoothSeamProbability.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SmoothSeamProbability.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma planar_radial_strip_gain_first {A : Set TransverseProduct} (hA : IsOpen A)
--       (hd : PlanarRadialDownset A) (hin : planarAxisPoint (1/2)∈A)
--       (hout : planarFirstAxisPoint (1/2)∉closure A)
--       {e j : ℝ} (he : 0≤e) (hj : j∈Icc 0 (21/100 : ℝ))
--       (hedge : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e)
--       (hgap : j≤volume.real A-e) :
--       ENNReal.ofReal (2*(1+(27/20)*j^2))≤planarTorusPerimeter A
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.PlanarRadialDownset`, `OAI.CubicTorus.TransverseProduct`, `OAI.CubicTorus.planarAxisPoint`, `OAI.CubicTorus.planarFirstAxisPoint` and `OAI.CubicTorus.planarTorusPerimeter` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_section_improved_profile` and `OAI.CubicTorus.planar_radial_strip_gain_second` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SmoothSeamProbability.lean (declaration OAI.CubicTorus.planar_radial_strip_gain_first)

import Mathlib
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

lemma planar_radial_strip_gain_first {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (hin : planarAxisPoint (1/2)∈A)
    (hout : planarFirstAxisPoint (1/2)∉closure A)
    {e j : ℝ} (he : 0≤e) (hj : j∈Icc 0 (21/100 : ℝ))
    (hedge : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e)
    (hgap : j≤volume.real A-e) :
    ENNReal.ofReal (2*(1+(27/20)*j^2))≤planarTorusPerimeter A := by
  sorry

end CubicTorus

end
end

end

end OAI
end

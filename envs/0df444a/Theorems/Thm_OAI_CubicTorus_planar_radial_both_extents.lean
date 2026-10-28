-- Prove2me | Theorems.Thm_OAI_CubicTorus_planar_radial_both_extents
-- name    : OAI.CubicTorus.planar_radial_both_extents
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:20:32.145866+00:00
-- url     : https://prove2.me/theorems/37956b50-4152-4c1c-b891-0f7dbd9e233b
-- title:
--   OAI.CubicTorus.planar_radial_both_extents: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.planar_radial_both_extents` of [lean/OAI/Geometry/CubicTorus/Reflection/AxialAreaDensity.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/AxialAreaDensity.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem planar_radial_both_extents {A : Set TransverseProduct} (hA : IsOpen A)
--       (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
--       (hout0 : planarFirstAxisPoint (1/2)∉closure A)
--       (hout1 : planarAxisPoint (1/2)∉closure A) (j : Fin 2) :
--       ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
--         (∀ y∈A,‖y j‖<L) ∧
--         (∀ y : TransverseProduct,(∀ k : Fin 2,k≠j →y k=0) →‖y j‖<L →y∈A) ∧
--         ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.PlanarRadialDownset`, `OAI.CubicTorus.TransverseProduct`, `OAI.CubicTorus.planarAxisPoint`, `OAI.CubicTorus.planarFirstAxisPoint` and `OAI.CubicTorus.planarTorusPerimeter` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_bottom_both_extents` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/AxialAreaDensity.lean (declaration OAI.CubicTorus.planar_radial_both_extents)

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

theorem planar_radial_both_extents {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout0 : planarFirstAxisPoint (1/2)∉closure A)
    (hout1 : planarAxisPoint (1/2)∉closure A) (j : Fin 2) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y j‖<L) ∧
      (∀ y : TransverseProduct,(∀ k : Fin 2,k≠j →y k=0) →‖y j‖<L →y∈A) ∧
      ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  sorry

end CubicTorus

end
end

end

end OAI
end

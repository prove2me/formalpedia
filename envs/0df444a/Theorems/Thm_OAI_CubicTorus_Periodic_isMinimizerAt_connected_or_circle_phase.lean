-- Prove2me | Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_connected_or_circle_phase
-- name    : OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:46:40.459603+00:00
-- url     : https://prove2.me/theorems/4f379a5f-07e6-4e68-a448-feb55064360e
-- title:
--   OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase` of [lean/OAI/Geometry/CubicTorus/Estimates/LatticeHeightHom.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/LatticeHeightHom.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem Periodic.isMinimizerAt_connected_or_circle_phase {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       IsPreconnected (frontier (openRepresentative E)) ∨
--         ∃ (m : Fin 3 → ℤ) (K : Set (AddCircle (1 : ℝ))),m≠0 ∧ IsOpen K ∧
--           openRepresentative E=(integerCharacter m) ⁻¹' K ∧
--           volume K=ENNReal.ofReal V
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.integerCharacter` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/LatticeHeightHom.lean (declaration OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase)

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem Periodic.isMinimizerAt_connected_or_circle_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ (m : Fin 3 → ℤ) (K : Set (AddCircle (1 : ℝ))),m≠0 ∧ IsOpen K ∧
        openRepresentative E=(integerCharacter m) ⁻¹' K ∧
        volume K=ENNReal.ofReal V := by
  sorry

end CubicTorus

end
end

end

end OAI
end

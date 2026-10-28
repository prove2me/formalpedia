-- Prove2me | Theorems.Thm_OAI_CubicTorus_first_transition_nonstandard_monotone_revolution
-- name    : OAI.CubicTorus.first_transition_nonstandard_monotone_revolution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:55:36.309869+00:00
-- url     : https://prove2.me/theorems/7f64e872-24d9-4653-811a-46ac2f9ad830
-- title:
--   OAI.CubicTorus.first_transition_nonstandard_monotone_revolution: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.first_transition_nonstandard_monotone_revolution` of [lean/OAI/Geometry/CubicTorus/Reflection/RevolutionTangents.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/RevolutionTangents.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem first_transition_nonstandard_monotone_revolution
--       {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
--       (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
--       ∃ (G : Set Torus) (b : Fin 3 → Bool) (r : ℝ × ℝ → ℝ),
--         MeasurableSet G ∧ IsMinimizerAt (4*Real.pi/81) G ∧
--         ¬SmallStandardRegion (4*Real.pi/81) G ∧
--         TrueRadialTube G (chamberCorner b) r ∧
--         (∀ i : Fin 3, coordinateReflection i ⁻¹' G =ᵐ[torusVolume] G) ∧
--         (∀ t a,r (t,a)=r (t,0)) ∧
--         (∀ t a,r (-t,a)=r (t,a)) ∧
--         ∀ t∈Ioo (chamberCorner b 0) (chamberCorner b 0+1/2),
--           deriv (fun s => r (s,0)) t<0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.TrueRadialTube`, `OAI.CubicTorus.chamberCorner` and `OAI.CubicTorus.coordinateReflection` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.SmallStandardRegion`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_first_transition_standard` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/RevolutionTangents.lean (declaration OAI.CubicTorus.first_transition_nonstandard_monotone_revolution)

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

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem first_transition_nonstandard_monotone_revolution
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (G : Set Torus) (b : Fin 3 → Bool) (r : ℝ × ℝ → ℝ),
      MeasurableSet G ∧ IsMinimizerAt (4*Real.pi/81) G ∧
      ¬SmallStandardRegion (4*Real.pi/81) G ∧
      TrueRadialTube G (chamberCorner b) r ∧
      (∀ i : Fin 3, coordinateReflection i ⁻¹' G =ᵐ[torusVolume] G) ∧
      (∀ t a,r (t,a)=r (t,0)) ∧
      (∀ t a,r (-t,a)=r (t,a)) ∧
      ∀ t∈Ioo (chamberCorner b 0) (chamberCorner b 0+1/2),
        deriv (fun s => r (s,0)) t<0 := by
  sorry

end CubicTorus

end
end

end OAI
end

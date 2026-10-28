-- Prove2me | Theorems.Thm_OAI_CubicTorus_TrueRadialTube_exists_rotation_zero
-- name    : OAI.CubicTorus.TrueRadialTube.exists_rotation_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:48:54.727116+00:00
-- url     : https://prove2.me/theorems/21f16c7b-227a-4b13-8ec4-c2ad1efd085f
-- title:
--   OAI.CubicTorus.TrueRadialTube.exists_rotation_zero: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.TrueRadialTube.exists_rotation_zero` of [lean/OAI/Geometry/CubicTorus/Profiles/FlatTranslation.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FlatTranslation.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem TrueRadialTube.exists_rotation_zero {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
--       (b : Fin 3 → Bool) {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E (chamberCorner b) r)
--       (hs₁ : coordinateReflection 1 ⁻¹' E =ᵐ[torusVolume] E)
--       (hs₂ : coordinateReflection 2 ⁻¹' E =ᵐ[torusVolume] E) :
--       ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
--         (_hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hNp : ∀ m x,N (x+latticeVector m)=N x),
--         IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
--         ∀ p, let x := coordinateSectionPoint (chamberCorner b) p.1 (r p • unitAngle p.2)
--           (r p • unitAngle p.2).re * N x 2 - (r p • unitAngle p.2).im * N x 1 = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.TrueRadialTube`, `OAI.CubicTorus.chamberCorner`, `OAI.CubicTorus.coordinateReflection`, `OAI.CubicTorus.coordinateSectionPoint` and `OAI.CubicTorus.unitAngle` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.first_transition_nonstandard_monotone_revolution` and `OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FlatTranslation.lean (declaration OAI.CubicTorus.TrueRadialTube.exists_rotation_zero)

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

theorem TrueRadialTube.exists_rotation_zero {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    (b : Fin 3 → Bool) {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E (chamberCorner b) r)
    (hs₁ : coordinateReflection 1 ⁻¹' E =ᵐ[torusVolume] E)
    (hs₂ : coordinateReflection 2 ⁻¹' E =ᵐ[torusVolume] E) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hNp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ p, let x := coordinateSectionPoint (chamberCorner b) p.1 (r p • unitAngle p.2)
        (r p • unitAngle p.2).re * N x 2 - (r p • unitAngle p.2).im * N x 1 = 0 := by
  sorry

end CubicTorus

end
end

end OAI
end

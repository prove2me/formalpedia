-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normalGraph_good_energy
-- name    : OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:06:45.728113+00:00
-- url     : https://prove2.me/theorems/1740426c-96a3-46db-ae52-3a6309caf6a1
-- title:
--   OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy` of [lean/OAI/Geometry/CubicTorus/Estimates/BVGraphEnergy.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVGraphEnergy.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter Metric`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_normalGraph_good_energy {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       ∃ C : ℝ≥0∞, C < ⊤ ∧
--         ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
--         ∀ N : Torus → Cover, Measurable N →
--           (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
--           (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
--         ∀ n : Cover, ‖n‖ = 1 → ∀ g : Plane → ℝ, ∀ K : ℝ≥0,
--           LipschitzWith K g → K ≤ 1 → ∀ (a : Torus) (D : Set Plane), MeasurableSet D →
--           (∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4) →
--           (∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ frontier (openRepresentative E)) →
--         ∀ U : Set Torus, MeasurableSet U →
--           (∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ U) →
--         (∫⁻ x in D, ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) ∂(volume : Measure Plane)) ≤
--           C * ∫⁻ b in U, ENNReal.ofReal (‖N b - n‖ ^ 2) ∂(spatialNormalMeasure μ : Measure Torus)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.normalGraph`, `OAI.CubicTorus.openRepresentative` and `OAI.CubicTorus.spatialNormalMeasure` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVGraphEnergy.lean (declaration OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normalGraph_good_energy {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ n : Cover, ‖n‖ = 1 → ∀ g : Plane → ℝ, ∀ K : ℝ≥0,
        LipschitzWith K g → K ≤ 1 → ∀ (a : Torus) (D : Set Plane), MeasurableSet D →
        (∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4) →
        (∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ frontier (openRepresentative E)) →
      ∀ U : Set Torus, MeasurableSet U →
        (∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ U) →
      (∫⁻ x in D, ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) ∂(volume : Measure Plane)) ≤
        C * ∫⁻ b in U, ENNReal.ofReal (‖N b - n‖ ^ 2) ∂(spatialNormalMeasure μ : Measure Torus) := by
  sorry

end CubicTorus

end
end

end

end OAI
end

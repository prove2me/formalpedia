-- Prove2me | Theorems.Thm_OAI_CubicTorus_MovingCenter_isMinimizerAt_moving_normal_modulus
-- name    : OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:44:57.665972+00:00
-- url     : https://prove2.me/theorems/add9b8ab-f4ca-438b-9124-2a0a03f674c6
-- title:
--   OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus` of [lean/OAI/Geometry/CubicTorus/Regularity/BVFlatBlowupRegular.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVFlatBlowupRegular.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.MovingCenter`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_moving_normal_modulus {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
--       ∃ r₀ C K ρ : ℝ, 0 < r₀ ∧ 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧
--         ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
--         ∀ N : Torus → Cover, Measurable N →
--           (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
--           (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
--         ∃ δ : ℝ, 0 < δ ∧ ∀ (c₀ : Cover), ‖c₀-cubeCenter‖ ≤ 1/16 → ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖ = 1 →
--           0 < r → r ≤ r₀ → 0 < e → e ≤ δ → r/e^2 ≤ δ →
--           (∫ x in Metric.closedBall (quotientMap c₀) (17*r), ‖N x-n₀‖^2
--             ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
--         ∃ ν : Cover → Cover,
--           ContinuousOn ν (quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128)) ∧
--           (∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
--             ‖ν a‖ = 1 ∧ ‖n₀-ν a‖ ≤ C*e ∧
--             BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) (ν a)) ∧
--           ∀ i : ℕ, ∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
--             ∀ b ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
--               dist a b ≤ ρ^i*(r/2) → dist (ν a) (ν b) ≤ K*e*(1/2 : ℝ)^i
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.BoundaryFlatAt`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.openRepresentative` and `OAI.CubicTorus.spatialNormalMeasure` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_C1_modulus` and `OAI.CubicTorus.actual_primary_fixed_scale_packets` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVFlatBlowupRegular.lean (declaration OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_moving_normal_modulus {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
    ∃ r₀ C K ρ : ℝ, 0 < r₀ ∧ 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (c₀ : Cover), ‖c₀-cubeCenter‖ ≤ 1/16 → ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖ = 1 →
        0 < r → r ≤ r₀ → 0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap c₀) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ ν : Cover → Cover,
        ContinuousOn ν (quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128)) ∧
        (∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          ‖ν a‖ = 1 ∧ ‖n₀-ν a‖ ≤ C*e ∧
          BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) (ν a)) ∧
        ∀ i : ℕ, ∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          ∀ b ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
            dist a b ≤ ρ^i*(r/2) → dist (ν a) (ν b) ≤ K*e*(1/2 : ℝ)^i := by
  sorry

end CubicTorus.MovingCenter

end
end

end

end OAI
end

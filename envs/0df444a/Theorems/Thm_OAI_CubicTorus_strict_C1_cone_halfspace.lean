-- Prove2me | Theorems.Thm_OAI_CubicTorus_strict_C1_cone_halfspace
-- name    : OAI.CubicTorus.strict_C1_cone_halfspace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:22:57.516591+00:00
-- url     : https://prove2.me/theorems/b53701f4-caa0-4aff-a901-0442c9ed2728
-- title:
--   OAI.CubicTorus.strict_C1_cone_halfspace: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.strict_C1_cone_halfspace` of [lean/OAI/Geometry/CubicTorus/Regularity/TorusC1Boundary.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/TorusC1Boundary.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem strict_C1_cone_halfspace {A : Set Cover} (hA : MeasurableSet A)
--       {ν : FiniteMeasure BlowupNormalBundle}
--       (heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) 1) =
--         (ν : Measure BlowupNormalBundle) {z | z.1∈Metric.closedBall (0 : Cover) 1})
--       (hcone : ∀ t : ℝ, 1≤t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
--         (t⁻¹ • x ∈ A ↔ x ∈ A))
--       (hC : ∀ p : Cover, ‖p‖<1 → p≠0 → p∈coverEssentialBoundary A → CoverC1BoundaryAt A p)
--       (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
--         tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
--         (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle))=0 ∧
--         (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
--       (h0 : (0 : Cover)∈coverEssentialBoundary A) :
--       ∃ n : Cover, ‖n‖=1 ∧ ∀ᵐ x ∂(volume : Measure Cover), x∈Metric.ball (0 : Cover) 1 →
--         (x∈A ↔ 0<⟪n,x⟫)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.BlowupNormalBundle`, `OAI.CubicTorus.CoverC1BoundaryAt`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.coverEssentialBoundary`, `OAI.CubicTorus.coverLocalPerimeter` and `OAI.CubicTorus.tangentialDivergence` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover` and `OAI.CubicTorus.divergence` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_centered_C1_modulus` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/TorusC1Boundary.lean (declaration OAI.CubicTorus.strict_C1_cone_halfspace)

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

theorem strict_C1_cone_halfspace {A : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) 1) =
      (ν : Measure BlowupNormalBundle) {z | z.1∈Metric.closedBall (0 : Cover) 1})
    (hcone : ∀ t : ℝ, 1≤t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    (hC : ∀ p : Cover, ‖p‖<1 → p≠0 → p∈coverEssentialBoundary A → CoverC1BoundaryAt A p)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle))=0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (h0 : (0 : Cover)∈coverEssentialBoundary A) :
    ∃ n : Cover, ‖n‖=1 ∧ ∀ᵐ x ∂(volume : Measure Cover), x∈Metric.ball (0 : Cover) 1 →
      (x∈A ↔ 0<⟪n,x⟫) := by
  sorry

end CubicTorus

end
end

end

end OAI
end

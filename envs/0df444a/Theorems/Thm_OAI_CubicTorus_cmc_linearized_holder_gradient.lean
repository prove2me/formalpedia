-- Prove2me | Theorems.Thm_OAI_CubicTorus_cmc_linearized_holder_gradient
-- name    : OAI.CubicTorus.cmc_linearized_holder_gradient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:53:07.072047+00:00
-- url     : https://prove2.me/theorems/df51da2d-dc74-4d22-9cb2-8305697595de
-- title:
--   OAI.CubicTorus.cmc_linearized_holder_gradient: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.cmc_linearized_holder_gradient` of [lean/OAI/Geometry/CubicTorus/Estimates/InteriorBallSubset.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/InteriorBallSubset.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem cmc_linearized_holder_gradient {p : Plane → Plane} (hp : Continuous p)
--       (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
--       (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
--         ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
--       (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
--       (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
--       (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
--         tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
--       ∃ H : Plane → Plane,∃ s K β : ℝ,0 < s ∧ s≤R/4 ∧ 0≤K ∧ 0<β ∧ β≤1 ∧
--         ContinuousOn H (Metric.ball 0 s) ∧
--         H =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (G : Plane → Plane) ∧
--         ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
--           dist (H x) (H y)≤K*(dist x y)^β
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.Plane`, `OAI.CubicTorus.PlaneWeakGradient` and `OAI.CubicTorus.cmcJacobian` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proofs of `OAI.CubicTorus.cmc_weak_continuous_C1`, `OAI.CubicTorus.isMinimizerAt_smooth_CMC`, `OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear` and `OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/InteriorBallSubset.lean (declaration OAI.CubicTorus.cmc_linearized_holder_gradient)

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

theorem cmc_linearized_holder_gradient {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ H : Plane → Plane,∃ s K β : ℝ,0 < s ∧ s≤R/4 ∧ 0≤K ∧ 0<β ∧ β≤1 ∧
      ContinuousOn H (Metric.ball 0 s) ∧
      H =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (G : Plane → Plane) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (H x) (H y)≤K*(dist x y)^β := by
  sorry

end CubicTorus

end
end

end

end OAI
end

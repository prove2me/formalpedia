-- Prove2me | Theorems.Thm_OAI_CubicTorus_cmc_weak_continuous_C1
-- name    : OAI.CubicTorus.cmc_weak_continuous_C1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:53:20.280674+00:00
-- url     : https://prove2.me/theorems/22df8958-c441-4ec0-817a-69e2bb8d3dde
-- title:
--   OAI.CubicTorus.cmc_weak_continuous_C1: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.cmc_weak_continuous_C1` of [lean/OAI/Geometry/CubicTorus/Profiles/PlanarWeakGradient.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/PlanarWeakGradient.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem cmc_weak_continuous_C1 {p : Plane → Plane} (hp : Continuous p)
--       (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
--       (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
--         ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
--       {u : Plane → ℝ} {G : Plane → Plane}
--       (hu : MemLp u 2 volume) (hG : MemLp G 2 volume)
--       (hc : ContinuousOn u (Metric.ball 0 R))
--       (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
--       (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
--         tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
--       ∃ s K β : ℝ,0 < s ∧ s≤R/16 ∧ 0≤K ∧ 0<β ∧ β≤1 ∧
--         ContDiffOn ℝ 1 u (Metric.ball 0 s) ∧
--         ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
--           dist (fderiv ℝ u x) (fderiv ℝ u y)≤K*(dist x y)^β
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.Plane`, `OAI.CubicTorus.PlaneWeakGradient` and `OAI.CubicTorus.cmcJacobian` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proof of `OAI.CubicTorus.CenteredJacobiChart.nodal_truncation_impossible` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/PlanarWeakGradient.lean (declaration OAI.CubicTorus.cmc_weak_continuous_C1)

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

theorem cmc_weak_continuous_C1 {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    {u : Plane → ℝ} {G : Plane → Plane}
    (hu : MemLp u 2 volume) (hG : MemLp G 2 volume)
    (hc : ContinuousOn u (Metric.ball 0 R))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ s K β : ℝ,0 < s ∧ s≤R/16 ∧ 0≤K ∧ 0<β ∧ β≤1 ∧
      ContDiffOn ℝ 1 u (Metric.ball 0 s) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (fderiv ℝ u x) (fderiv ℝ u y)≤K*(dist x y)^β := by
  sorry

end CubicTorus

end
end

end

end OAI
end

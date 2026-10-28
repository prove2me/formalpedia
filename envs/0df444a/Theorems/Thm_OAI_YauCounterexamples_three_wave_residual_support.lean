-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_wave_residual_support
-- name    : OAI.YauCounterexamples.three_wave_residual_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:14:49.204505+00:00
-- url     : https://prove2.me/theorems/e57bebac-e926-4175-935e-cb9acc67dc84
-- title:
--   OAI.YauCounterexamples.three_wave_residual_support: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_wave_residual_support` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   lemma three_wave_residual_support (g : SmoothMetric ThreeModel ThreeManifold)
--       {F : Set ThreeManifold} (hF : IsClosed F) {r : ℝ}
--       (hFr : F⊆threeNormalInv '' closedBall 0 r)
--       (hext : ∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
--         g.inner q v w=threeBackgroundMetric.inner q v w)
--       {u : NormalWaveSpace → ℝ} (_hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
--       (hs : tsupport u⊆closedBall 0 r) {k : ℕ} (hk : 2 ≤ k) :
--       tsupport (fun q => laplaceBeltrami g (threeCoupled threeCouplingRadius k+threeWaveLift u) q+
--         productFrequency k*(threeCoupled threeCouplingRadius k+threeWaveLift u) q)⊆
--         threeNormalInv '' closedBall 0 r
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.productFrequency` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeBackgroundMetric` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCoupled` and `OAI.YauCounterexamples.threeWaveLift` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_exact_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean (declaration OAI.YauCounterexamples.three_wave_residual_support)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma three_wave_residual_support (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set ThreeManifold} (hF : IsClosed F) {r : ℝ}
    (hFr : F⊆threeNormalInv '' closedBall 0 r)
    (hext : ∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
      g.inner q v w=threeBackgroundMetric.inner q v w)
    {u : NormalWaveSpace → ℝ} (_hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hs : tsupport u⊆closedBall 0 r) {k : ℕ} (hk : 2 ≤ k) :
    tsupport (fun q => laplaceBeltrami g (threeCoupled threeCouplingRadius k+threeWaveLift u) q+
      productFrequency k*(threeCoupled threeCouplingRadius k+threeWaveLift u) q)⊆
      threeNormalInv '' closedBall 0 r := by
  sorry
end

open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

end YauCounterexamples
end

end OAI
end

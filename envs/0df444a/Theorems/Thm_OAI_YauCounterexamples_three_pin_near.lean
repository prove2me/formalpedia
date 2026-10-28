-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_pin_near
-- name    : OAI.YauCounterexamples.three_pin_near
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:14:10.108974+00:00
-- url     : https://prove2.me/theorems/054cba04-a313-49b9-908a-3e7d17922f3a
-- title:
--   OAI.YauCounterexamples.three_pin_near: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_pin_near` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   theorem three_pin_near
--       (g : SmoothMetric ThreeModel ThreeManifold) {R b c : ℝ} (hR : 0<R)
--       (hclean : ThreeCleanBall R) (hb0 : 0<b) (hbc : b < c) (hc : c<R/2)
--       (hext : ThreeExterior g b) {m : ℕ} (hm : 1 ≤ m)
--       (u : ThreeManifold → ℝ) (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
--       (hue : ∀ q, -laplaceBeltrami g u q=productFrequency (4*m+1)*u q)
--       (hout : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius (4*m+1) q)
--       (U : Set (ThreeTensor R)) (hU : IsOpen U)
--       (hgU : threeTensorOf R g (hext.mono (hbc.trans hc).le) ∈ U) :
--       ∃ h : SmoothMetric ThreeModel ThreeManifold, ∃ he : ThreeExterior h c,
--         threeTensorOf R h (he.mono hc.le) ∈ U ∧
--         (∀ q, -laplaceBeltrami h u q=productFrequency (4*m+1)*u q) ∧
--         ThreeSimple h u (productFrequency (4*m+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.MetricForm` and `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.productFrequency` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.ThreeCleanBall`, `OAI.YauCounterexamples.ThreeExterior`, `OAI.YauCounterexamples.ThreeSimple`, `OAI.YauCounterexamples.ThreeTensor`, `OAI.YauCounterexamples.threeAmbientFormNorm`, `OAI.YauCounterexamples.threeAmbientFormSpace`, `OAI.YauCounterexamples.threeNormalInv`, `OAI.YauCounterexamples.threeTensorSupport` and `OAI.YauCounterexamples.ThreeExterior.mono` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCoupled` and `OAI.YauCounterexamples.threeTensorOf` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_simple_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean (declaration OAI.YauCounterexamples.three_pin_near)

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
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal

local instance threePinFormNorm_r90f345_1 : NormedAddCommGroup (MetricForm ThreeModel) := inferInstanceAs (NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threePinFormSpace_r90f345_1 : NormedSpace ℝ (MetricForm ThreeModel) := inferInstanceAs (NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
theorem three_pin_near
    (g : SmoothMetric ThreeModel ThreeManifold) {R b c : ℝ} (hR : 0<R)
    (hclean : ThreeCleanBall R) (hb0 : 0<b) (hbc : b < c) (hc : c<R/2)
    (hext : ThreeExterior g b) {m : ℕ} (hm : 1 ≤ m)
    (u : ThreeManifold → ℝ) (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ q, -laplaceBeltrami g u q=productFrequency (4*m+1)*u q)
    (hout : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius (4*m+1) q)
    (U : Set (ThreeTensor R)) (hU : IsOpen U)
    (hgU : threeTensorOf R g (hext.mono (hbc.trans hc).le) ∈ U) :
    ∃ h : SmoothMetric ThreeModel ThreeManifold, ∃ he : ThreeExterior h c,
      threeTensorOf R h (he.mono hc.le) ∈ U ∧
      (∀ q, -laplaceBeltrami h u q=productFrequency (4*m+1)*u q) ∧
      ThreeSimple h u (productFrequency (4*m+1)) := by
  sorry
end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

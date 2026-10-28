-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_wave_exterior_germ
-- name    : OAI.YauCounterexamples.three_wave_exterior_germ
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:14:21.950427+00:00
-- url     : https://prove2.me/theorems/f5eb1f68-ada4-4282-9da1-d5bdb934c1ba
-- title:
--   OAI.YauCounterexamples.three_wave_exterior_germ: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_wave_exterior_germ` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   lemma three_wave_exterior_germ {u : NormalWaveSpace → ℝ} (hc : HasCompactSupport u)
--       {r : ℝ} (hs : tsupport u⊆closedBall 0 r) (k : ℕ) {q : ThreeManifold}
--       (hq : q∉threeNormalInv '' closedBall 0 r) :
--       threeCoupled threeCouplingRadius k+threeWaveLift u =ᶠ[𝓝 q] threeCoupled threeCouplingRadius k
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCoupled` and `OAI.YauCounterexamples.threeWaveLift` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.exists_three_exact_stage`, `OAI.YauCounterexamples.three_annular_projection_uniform` and `OAI.YauCounterexamples.three_wave_residual_support` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean (declaration OAI.YauCounterexamples.three_wave_exterior_germ)

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
lemma three_wave_exterior_germ {u : NormalWaveSpace → ℝ} (hc : HasCompactSupport u)
    {r : ℝ} (hs : tsupport u⊆closedBall 0 r) (k : ℕ) {q : ThreeManifold}
    (hq : q∉threeNormalInv '' closedBall 0 r) :
    threeCoupled threeCouplingRadius k+threeWaveLift u =ᶠ[𝓝 q] threeCoupled threeCouplingRadius k := by
  sorry
end

open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

end YauCounterexamples
end

end OAI
end

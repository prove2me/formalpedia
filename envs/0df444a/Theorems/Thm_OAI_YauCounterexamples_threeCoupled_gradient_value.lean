-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_threeCoupled_gradient_value
-- name    : OAI.YauCounterexamples.threeCoupled_gradient_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:11:36.917991+00:00
-- url     : https://prove2.me/theorems/e41ea97c-1430-4801-bb36-1afe8c30d92e
-- title:
--   OAI.YauCounterexamples.threeCoupled_gradient_value: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.threeCoupled_gradient_value` of [lean/OAI/Geometry/SmoothYau/Geometry/ThreeProjectionNormedSpace.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ThreeProjectionNormedSpace.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Module`, `open scoped Topology ContDiff InnerProductSpace Matrix`):
--
--   ```lean
--   lemma threeCoupled_gradient_value (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold) :
--       coordinateGradientPair threeBackgroundMetric (threeCoupled r k) (threeCoupled r k) p=
--         (k:ℝ)^2*((( (p.2:ℂ)^k*productA p.1^(k-1)).re+
--           ((p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)).re)^2+
--           ((p.2:ℂ)^k*productA p.1^(k-1)).im^2+
--           ((p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)).im^2-
--           (threeCoupled r k p)^2+(threeCoupledComplex r k p).im^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.productA`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeBackgroundMetric` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.productB` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.threeCoupled` and `OAI.YauCounterexamples.threeCoupledComplex` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.exists_threeInteriorMeridianEnergy_deriv`, `OAI_YauCounterexamples_threeCoupled_clean_gradient_lower`, `OAI.YauCounterexamples.threeCoupled_conjugate_gradient_lower`, `OAI_YauCounterexamples_threeCoupled_profile_rank_dense`, `OAI_YauCounterexamples_threeInteriorMeridianEnergy_right`, `OAI_YauCounterexamples_threeInteriorMeridianEnergy_zero`, `OAI.YauCounterexamples.three_clean_collar_gradient`, `OAI.YauCounterexamples.three_clean_conjugating_margin` and `OAI.YauCounterexamples.three_collar_rank` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ThreeProjectionNormedSpace.lean (declaration OAI.YauCounterexamples.threeCoupled_gradient_value)

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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
lemma threeCoupled_gradient_value (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold) :
    coordinateGradientPair threeBackgroundMetric (threeCoupled r k) (threeCoupled r k) p=
      (k:ℝ)^2*((( (p.2:ℂ)^k*productA p.1^(k-1)).re+
        ((p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)).re)^2+
        ((p.2:ℂ)^k*productA p.1^(k-1)).im^2+
        ((p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)).im^2-
        (threeCoupled r k p)^2+(threeCoupledComplex r k p).im^2) := by
  sorry
end

open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

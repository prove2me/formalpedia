-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_threeCoupled_global_noncancellation
-- name    : OAI.YauCounterexamples.threeCoupled_global_noncancellation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:11:10.107213+00:00
-- url     : https://prove2.me/theorems/ea986201-a912-4c5b-b265-15374c5916ab
-- title:
--   OAI.YauCounterexamples.threeCoupled_global_noncancellation: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.threeCoupled_global_noncancellation` of [lean/OAI/Geometry/SmoothYau/Estimates/ThreeNoncancelNormedSpace.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ThreeNoncancelNormedSpace.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Module`, `open scoped Topology ContDiff InnerProductSpace Matrix`):
--
--   ```lean
--   theorem threeCoupled_global_noncancellation {r : ℝ} (hr : 0 < r) (hr8 : r≤1/8)
--       (k : ℕ) (hk : 2≤k) (p : ThreeManifold) :
--       productWeight r k p ≤ 12*(|threeCoupled r k p|+
--         ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel` and `OAI.YauCounterexamples.threeChartedSpace` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.productWeight` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.threeNoncancelNormedSpace` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.threeCoupled` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.three_exterior_intrinsic_margin` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ThreeNoncancelNormedSpace.lean (declaration OAI.YauCounterexamples.threeCoupled_global_noncancellation)

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

open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix

attribute [local instance] OAI.YauCounterexamples.threeNoncancelNormedSpace
local instance threeNoncancelContinuousSMul_r1a928a_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem threeCoupled_global_noncancellation {r : ℝ} (hr : 0 < r) (hr8 : r≤1/8)
    (k : ℕ) (hk : 2≤k) (p : ThreeManifold) :
    productWeight r k p ≤ 12*(|threeCoupled r k p|+
      ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ)) := by
  sorry

end YauCounterexamples
end

end OAI
end

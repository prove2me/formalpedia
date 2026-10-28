-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_threeCoupled_ambient_derivative
-- name    : OAI.YauCounterexamples.threeCoupled_ambient_derivative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:09:52.095987+00:00
-- url     : https://prove2.me/theorems/17970233-8e68-485a-b039-1b9905551bbb
-- title:
--   OAI.YauCounterexamples.threeCoupled_ambient_derivative: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.threeCoupled_ambient_derivative` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFormulaNormedSpace.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFormulaNormedSpace.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Module`, `open scoped Topology ContDiff InnerProductSpace Matrix`):
--
--   ```lean
--   lemma threeCoupled_ambient_derivative (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold)
--       (v : ThreeModel) :
--       fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 v=
--         inner ℝ (unitSphereFrame (n:=2) p.1 v.fst) (threeAmbientSphereGradient r k p)+
--         inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) (threeAmbientCircleGradient r k p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.circle_dimension_fact` and `OAI.YauCounterexamples.threeChartedSpace` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.threeFormula_dimension_fact` and `OAI.YauCounterexamples.unitSphereFrame` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeAmbientCircleGradient`, `OAI.YauCounterexamples.threeAmbientSphereGradient` and `OAI.YauCounterexamples.threeCoupled` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_threeCoupled_gradient_chart_analytic` and `OAI.YauCounterexamples.threeCoupled_gradient_value` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFormulaNormedSpace.lean (declaration OAI.YauCounterexamples.threeCoupled_ambient_derivative)

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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples

attribute [local instance] OAI.YauCounterexamples.threeFormula_dimension_fact
lemma threeCoupled_ambient_derivative (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold)
    (v : ThreeModel) :
    fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 v=
      inner ℝ (unitSphereFrame (n:=2) p.1 v.fst) (threeAmbientSphereGradient r k p)+
      inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) (threeAmbientCircleGradient r k p) := by
  sorry
end YauCounterexamples
end

end OAI
end

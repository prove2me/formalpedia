-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exists_generating_neighborhood
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.exists_generating_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:48:11.754097+00:00
-- url     : https://prove2.me/theorems/d0240d82-e9ff-438f-b58d-918dd156d3b6
-- title:
--   Generating chart actions exist near every chart state whose time-one flow stays in a chart (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`, $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$ whose distance is the Riemannian distance, and $c = d^2/2$ is the cost (`cost`). For a point $x$, `stateChart x` is the chart of the tangent bundle at $(x, 0)$. It gives a state $(z, u) \in TM$ coordinates $q = (q_1, q_2) \in \mathbb R^n \times \mathbb R^n$ (position and velocity). `geodesicFlow t` is the geodesic flow on $TM$. `crossFlowCoordinates x y t q` is the `stateChart y` coordinate of the state reached at time $t$ from the state with `stateChart x` coordinate $q$.
--
--   For $\varepsilon \in \mathbb R$, `GeneratingChartAction x y ε q` holds when all of the following do:
--   - $q$ lies in the target of `stateChart x`;
--   - the states reached at times $1 - \varepsilon$ and $1$ from the state $q$ lie in the source of `stateChart y`;
--   - `ShortChartAction y ε` holds at the time-$(1-\varepsilon)$ coordinate. That is, the chart cost at $y$ (`chartCost y`) is $C^\infty$ at the pair (position, position after a further time $\varepsilon$). Its derivative there is $\varepsilon$ times the difference of the metric pairings of the final and initial velocities with the two position variations: the first-variation formula for the final short step.
--
--   **Statement.** Let $x, y \in M$. Let $q$ be in the target of `stateChart x`, and suppose the state reached at time $1$ from $q$ lies in the source of `stateChart y`. Then there is $\varepsilon$ with $0 < \varepsilon < 1$ such that `GeneratingChartAction x y ε r` holds for every $r$ in a neighborhood of $q$.
--
--   The generating chart action is a Lean device. It splits the action of a geodesic of time one into a long first piece of time $1 - \varepsilon$ and a short final step of time $\varepsilon$, on which the cost is smooth and has its first-variation formula. The device replaces the Jacobi-field trial construction in the proof of Proposition 3.1 of the paper ("A trial-field estimate"). This statement supplies the neighborhoods on which it is defined. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.exists_generating_neighborhood`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/GeneratingNeighborhood.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and from the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/GeneratingNeighborhood.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.exists_generating_neighborhood)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem exists_generating_neighborhood (x y : M) {q : Model n × Model n}
    (hq : q ∈ (stateChart x).target)
    (hy : geodesicFlow 1 ((stateChart x).symm q) ∈ (stateChart y).source) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ r in 𝓝 q, GeneratingChartAction x y ε r := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

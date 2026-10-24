-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_generatingHessian_vertical_nonneg
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_vertical_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:48:39.287554+00:00
-- url     : https://prove2.me/theorems/ef3b4a32-390f-437e-9aea-8e0d58495d93
-- title:
--   The generating Hessian is nonnegative in vertical directions along a minimizing geodesic (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statements `OAI.WeakMTWGlobalSupport.WeakMTW.exists_generating_neighborhood` and `OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_focal` of this split:
--   - `stateChart x` gives states coordinates $q = (q_1, q_2)$.
--   - `GeneratingChartAction x y ε q` is the generating chart action condition.
--   - `generatingHessian x y ε q` is the second derivative of the generating action at $(q, z_1(q))$, where $z_1(q)$ is the endpoint coordinate of the time-one state.
--   - `geodesic p` is the complete geodesic with initial state $p$.
--
--   **Statement.** Let $0 < \varepsilon < 1$ and suppose `GeneratingChartAction x y ε q`. Let $p = (p_1, p_2)$ be the state with coordinate $q$, and suppose the geodesic from $p$ minimizes up to time $1$: $d(p_1, \gamma_p(1)) = \|p_2\|$. Then for every $\kappa \in \mathbb R^n$,
--   $$0 \le \mathrm{generatingHessian}_{x,y,\varepsilon}(q)\bigl(((0,\kappa),0),\ ((0,\kappa),0)\bigr).$$
--
--   The generating action never falls below the cost between its base point and its endpoint, and it equals that cost along a minimizing geodesic. So in the velocity variable, with base and endpoint fixed, it has a minimum. In the paper's proof of Proposition 3.1, the trial function $P(a) = Q_a(J_a, J_a)$ is nonnegative on minimizing velocities. This statement is the Lean counterpart of that nonnegativity for the generating action. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_vertical_nonneg`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/GeneratingHessian.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and from the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/GeneratingHessian.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_vertical_nonneg)

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
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem generatingHessian_vertical_nonneg (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {q : Model n × Model n} (hq : GeneratingChartAction x y ε q)
    (hm : dist ((stateChart x).symm q).1 (geodesic ((stateChart x).symm q) 1) = ‖((stateChart x).symm q).2‖)
    (κ : Model n) : 0 ≤ generatingHessian x y ε q ((0,κ),0) ((0,κ),0) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

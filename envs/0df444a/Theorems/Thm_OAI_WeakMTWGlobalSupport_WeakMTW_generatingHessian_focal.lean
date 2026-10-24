-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_generatingHessian_focal
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_focal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:50:46.774433+00:00
-- url     : https://prove2.me/theorems/e9428398-78a9-4565-82d0-67b7c1986be7
-- title:
--   The generating Hessian in a focal vertical direction (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statement `OAI.WeakMTWGlobalSupport.WeakMTW.exists_generating_neighborhood` of this split:
--   - $M$ is a compact Riemannian manifold.
--   - `stateChart x` gives states coordinates $q = (q_1, q_2)$ (position, velocity).
--   - `crossFlowCoordinates x y t q` is the chart-at-$y$ coordinate of the state reached at time $t$ from $q$.
--   - `GeneratingChartAction x y ε q` is the generating chart action condition.
--   - `metric x a` is the Riemannian metric in the chart at $x$, at the coordinate point $a$.
--
--   The **generating action** (`generatingAction x y ε`) is the function of a chart state $q$ and an endpoint coordinate $z$ given by
--   $$(q, z) \mapsto (1-\varepsilon)\,\tfrac12\,\mathrm{metric}_x(q_1)(q_2, q_2) + \varepsilon^{-1}\, c_y\bigl(\pi_1\,\mathrm{crossFlow}_{x,y}(1-\varepsilon, q),\ z\bigr),$$
--   with $c_y$ the cost in the chart at $y$ (`chartCost y`). It is the action of the geodesic piece of time $1-\varepsilon$, plus a final step to $z$ priced by the cost. The **generating Hessian** `generatingHessian x y ε q` is its second derivative at $(q, z_1(q))$, where $z_1(q)$ is the position coordinate of the time-one state from $q$.
--
--   **Statement.** Let $\varepsilon \ne 0$, and suppose `GeneratingChartAction x y ε r` holds for all $r$ near $q$. Let $\kappa \in \mathbb R^n$ be a focal vertical direction: the derivative of $r \mapsto z_1(r)$ at $q$ in the direction $(0, \kappa)$ vanishes. Then for all $a, b \in \mathbb R^n$,
--   $$\mathrm{generatingHessian}_{x,y,\varepsilon}(q)\bigl(((0,\kappa),0),\ ((a,b),0)\bigr) = -\,\mathrm{metric}_x(q_1)(\kappa, a).$$
--
--   In the paper's proof of Proposition 3.1 ("A trial-field estimate"), integration by parts gives $Q_z(E_z, J_z) = -\langle \xi, k\rangle_x$ for the Jacobi field $J_z$ of a kernel vector $k$ of $d_z\exp_x$. This statement is the Lean counterpart of that identity for the generating action. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_focal`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/GeneratingHessian.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and from the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/GeneratingHessian.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_focal)

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

 theorem generatingHessian_focal (x y : M) {ε : ℝ} (hε : ε ≠ 0) {q : Model n × Model n}
    (hq : ∀ᶠ r in 𝓝 q, GeneratingChartAction x y ε r) {κ : Model n}
    (hker : fderiv ℝ (fun r => (crossFlowCoordinates x y 1 r).1) q (0,κ) = 0)
    (a b : Model n) :
    generatingHessian x y ε q ((0,κ),0) ((a,b),0) = -metric x q.1 κ a := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_nonconjugate_inward_hessian_bound
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.nonconjugate_inward_hessian_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:49:26.302536+00:00
-- url     : https://prove2.me/theorems/22c9f9eb-7025-422b-b98c-34475b55877e
-- title:
--   The action Hessian is bounded below on inward radial contractions of a nonconjugate minimizing velocity (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$, whose distance is the Riemannian distance. In addition:
--   - `minimizingDomain x` is the closed minimizing domain $G_x = \{v \in T_xM : d(x, \exp_x v) = \|v\|\}$.
--   - `Nonconjugate x v` says that the derivative at $v$ of $w \mapsto \exp_x w$ (read in the chart at $\exp_x v$) is injective.
--   - The action Hessian `actionHessian x v` is the bilinear form on $T_xM$ from the statement `OAI.WeakMTWGlobalSupport.WeakMTW.generating_scalar_trial` of this split: the coordinate Hessian of $c(\cdot, \exp_x v)$ at $x$, plus the Christoffel term.
--
--   **Statement.** Let $v \in G_x$ be nonconjugate, and let $\xi \in T_xM$. Then there are $L \in \mathbb R$ and $\delta > 0$ such that for all $0 < h < \delta$,
--   $$-L \le \mathrm{actionHessian}_x\bigl((1-h)v\bigr)(\xi, \xi).$$
--
--   The paper's Section 2.1 notes that as velocities in $I(x)$ approach a nonconjugate minimizing velocity, their true-cost Hessians converge to its smooth branch Hessian. The proof of Proposition 3.1 uses this as follows: nonconjugacy at the endpoints of a segment bounds the Hessians at the contracted endpoints from below as $r \uparrow 1$. This statement is that lower bound along the inward radial contractions $(1-h)v$. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.nonconjugate_inward_hessian_bound`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/InwardHessianBound.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and from the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/InwardHessianBound.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.nonconjugate_inward_hessian_bound)

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

 theorem nonconjugate_inward_hessian_bound (x : M) {v : TangentSpace (model n) x}
    (hm : v ∈ minimizingDomain x) (hn : Nonconjugate x v) (ξ : TangentSpace (model n) x) :
    ∃ L δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      -L ≤ actionHessian x ((1-h)•v) ξ ξ := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

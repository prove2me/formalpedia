-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_ActionBranch_gradient_center
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.gradient_center
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:44:54.675022+00:00
-- url     : https://prove2.me/theorems/d6f5db1f-aad1-4c6a-a762-458f54fe7a0c
-- title:
--   First variation of the branch cost at its centre: the gradient is minus the velocity (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statement `OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.exists_of_nonconjugate` of this split: $M$ is a compact Riemannian manifold, and an action branch $B$ from $x$ to $y$ (`ActionBranch x y`) is a smooth local inverse $e$ of the exponential pair map $(z, u) \mapsto (z, \exp_z u)$ in charts. Its **value** `B.value` is the branch cost: at a point $q$ of chart coordinates $(a, b)$ it is half the squared norm of the inverse-branch velocity, $\tfrac12 g_a(u, u)$ where $e^{-1}(q) = (a, u)$ (`branchAction`, `chartKinetic`), with $g$ the metric read in the chart at $x$ (`metric x`). `tangentChartLinear x` is the derivative at $x$ of the chart at $x$, which identifies $T_xM$ with $\mathbb R^n$.
--
--   **Statement.** Let $B$ be an action branch from $x$ to $y$ whose source contains the tangent-bundle coordinates of $(x, v)$. Then for every $\xi \in T_xM$, the derivative of the branch cost at the chart point $(\varphi_x(x), \varphi_y(\exp_x v))$ in the direction (`tangentChartLinear x ξ`, 0), moving only the first endpoint, is
--   $$D\,\hat c\,(\xi, 0) = -\langle v, \xi\rangle .$$
--
--   This is the first-variation formula $\nabla_x \hat c(x, \exp_x w) = -w$ of the paper's Section 2.1. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.gradient_center`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/ActionBranch.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/ActionBranch.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.gradient_center)

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

 namespace ActionBranch
 variable {x y : M}

 theorem gradient_center (B : ActionBranch (n := n) x y) {v : TangentSpace (model n) x}
    (hve : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    (ξ : TangentSpace (model n) x) :
    fderiv ℝ B.value (chartAt (Model n) x x,chartAt (Model n) y (exp x v))
      (tangentChartLinear x ξ,0) = -inner ℝ v ξ := by
  sorry

 end ActionBranch
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

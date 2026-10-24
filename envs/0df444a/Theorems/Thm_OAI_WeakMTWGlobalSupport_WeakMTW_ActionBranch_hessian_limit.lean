-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_ActionBranch_hessian_limit
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.hessian_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:46:24.601793+00:00
-- url     : https://prove2.me/theorems/57ef3851-42e2-4d92-9c20-e63fd54b7826
-- title:
--   Cost Hessians converge to the branch Hessian at a nonconjugate velocity (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statements `OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.exists_of_nonconjugate` and `OAI.WeakMTWGlobalSupport.WeakMTW.actionHessian_eq_branch` of this split: $B$ is an action branch from $x$ to $y$ (a smooth local inverse of the exponential pair map in charts, with coordinate map `B.coord`). `actionHessian x w` is the coordinate covariant Hessian form at $x$ of the cost $c(\cdot, \exp_x w)$, and `branchHessianDiag x y B.coord v ξ` is the same expression for the branch cost of $B$, second endpoint fixed. `injectivityDomain x` is the set of velocities whose geodesic minimizes a little beyond time 1.
--
--   **Statement.** Let the source of $B$ contain the tangent-bundle coordinates of $(x, v)$, and let $\xi \in T_xM$. Let $w : \mathbb R \to T_xM$ and a filter $L$ on $\mathbb R$ satisfy $w(r) \to v$ along $L$, with $w(r) \in$ `injectivityDomain x` eventually along $L$. Then
--   $$\texttt{actionHessian}\ x\ (w(r))\ \xi\ \xi \;\longrightarrow\; \texttt{branchHessianDiag}\ x\ y\ B.\mathrm{coord}\ v\ \xi \quad\text{along } L .$$
--
--   This is the convergence statement of the paper's Section 2.1: as velocities in $I(x)$ approach a nonconjugate velocity, their true-cost Hessians converge to the branch Hessian. The limit velocity $v$ itself need not lie in the injectivity domain, so this covers minimizing cut velocities. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.hessian_limit`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/ActionBranch.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/ActionBranch.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.hessian_limit)

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

 theorem hessian_limit (B : ActionBranch (n := n) x y)
    {v : TangentSpace (model n) x}
    (hve : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    (ξ : TangentSpace (model n) x) {w : ℝ → TangentSpace (model n) x} {L : Filter ℝ}
    (hw : Tendsto w L (𝓝 v)) (hI : ∀ᶠ r in L, w r ∈ injectivityDomain x) :
    Tendsto (fun r => actionHessian x (w r) ξ ξ) L (𝓝 (branchHessianDiag x y B.coord v ξ)) := by
  sorry

 end ActionBranch
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

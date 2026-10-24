-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_ActionBranch_eq_cost_along
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.eq_cost_along
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:46:22.583811+00:00
-- url     : https://prove2.me/theorems/6b261e7e-4be5-4a0b-8ab7-aaf6999417d6
-- title:
--   Along sequences near an injectivity velocity, the branch cost is the cost (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statements `OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.exists_of_nonconjugate` and `OAI.WeakMTWGlobalSupport.WeakMTW.actionHessian_eq_branch` of this split: $B$ is an action branch from $x$ to $z$ (a smooth local inverse of the exponential pair map in charts), its value `B.value` is the branch cost, half the squared norm of the inverse-branch velocity, the cost is $c(p, q) = d(p, q)^2/2$ (`cost`), and `injectivityDomain x` is the set of velocities whose geodesic minimizes a little beyond time 1.
--
--   **Statement.** Let $v \in$ `injectivityDomain x`, with the tangent-bundle coordinates of $(x, v)$ in the source of $B$ and $\exp_x v$ in the source of the chart $\varphi_z$ at $z$. If $p_j \to x$ and $q_j \to \exp_x v$, then for all large $j$
--   $$B.\mathrm{value}\bigl(\varphi_x(p_j), \varphi_z(q_j)\bigr) = c(p_j, q_j) .$$
--
--   This is the sequential form of the remark of the paper's Section 2.1 that, for $w \in I(x)$, the branch cost agrees locally with the cost $c$ (via its Lemma 2.1). Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.eq_cost_along`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/CollisionGeometry.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/CollisionGeometry.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.eq_cost_along)

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

 theorem ActionBranch.eq_cost_along {x z : M} (B : ActionBranch (n := n) x z)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (he : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    {p q : ℕ → M} (hp : Tendsto p atTop (𝓝 x)) (hq : Tendsto q atTop (𝓝 (exp x v)))
    (hz : exp x v ∈ (chartAt (Model n) z).source) :
    ∀ᶠ j in atTop, B.value (chartAt (Model n) x (p j),chartAt (Model n) z (q j)) = cost (p j) (q j) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

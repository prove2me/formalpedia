-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_actionHessianDiag_smooth
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.actionHessianDiag_smooth
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-19T02:58:02.034658+00:00
-- url     : https://prove2.me/theorems/faca538a-3c06-4e3a-878d-c16897b5367a
-- title:
--   The diagonal cost Hessian is smooth on the injectivity domain (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`, $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$, and its metric-space distance is the Riemannian distance. `exp x v` is the endpoint at time $1$ of the complete geodesic with initial data $(x, v)$. The cost is $c(x, y) = d(x, y)^2/2$ (`cost`). The **injectivity domain** of $x$ is
--   $$I(x) = \{v \in T_xM : d(x, \exp_x(a v)) = a\|v\| \text{ for some } a > 1\}$$
--   (`injectivityDomain`): the velocities whose geodesic still minimizes a little beyond time $1$. For $u, \xi \in T_xM$, `actionHessianDiag x u ξ` is the second derivative at $t = 0$ of $t \mapsto c(\exp_x(t\xi), \exp_x u)$. That is the Hessian of $c(\cdot, \exp_x u)$ at $x$ in the direction $\xi$, taken along the geodesic through $x$ with velocity $\xi$.
--
--   **Statement.** Let $x \in M$, $v \in I(x)$ and $\xi \in T_xM$. Then the map
--   $$u \longmapsto \frac{d^2}{dt^2}\Big|_{t=0} c\bigl(\exp_x(t\xi), \exp_x u\bigr)$$
--   is $C^\infty$ near $v$.
--
--   The cost is smooth near pairs $(x, \exp_x v)$ with $v \in I(x)$, where the minimizing geodesic is unique and nonconjugate (the paper's Lemma 2.1). This statement is the form of that smoothness used to differentiate the MTW expression along lines of velocities, in the transverse concavity argument of the paper's Section 2 (Lemma 2.4). Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.actionHessianDiag_smooth`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/MTWConcavity.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/MTWConcavity.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.actionHessianDiag_smooth)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW002

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
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem actionHessianDiag_smooth (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x) :
    ContDiffAt ℝ ∞ (fun u => actionHessianDiag x u ξ) v := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

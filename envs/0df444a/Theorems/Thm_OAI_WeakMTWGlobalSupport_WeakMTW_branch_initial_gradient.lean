-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_branch_initial_gradient
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_gradient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:47:10.468276+00:00
-- url     : https://prove2.me/theorems/cb46ff55-7924-468b-8c0e-0b28d93ea61c
-- title:
--   First variation of the branch cost in the initial point (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statement `OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.exists_of_nonconjugate` of this split: $M$ is a compact Riemannian manifold, and `pairExpCoordinates x y` is the exponential pair map $(z, u) \mapsto (z, \exp_z u)$ read in the tangent-bundle chart at $x$ and the chart at $y$. For a local inverse $e$ of it, the branch cost `branchAction x e` at $q$ is $\tfrac12 g_a(u, u)$, where $e^{-1}(q) = (a, u)$ and $g$ is the metric read in the chart at $x$ (`metric x`).
--
--   **Statement.** Let $e$ be an open partial homeomorphism of $\mathbb R^n \times \mathbb R^n$ that agrees with `pairExpCoordinates x y`, has source inside `pairExpDomain x y` and a $C^\infty$ inverse on its target. For every $q = (a, b)$ in the target of $e$ and every $w \in \mathbb R^n$, the derivative in the first coordinate, with the second endpoint fixed at $b$, is
--   $$D_a\bigl[\,a' \mapsto \hat c(a', b)\,\bigr](w) = -\,g_a\bigl(u, w\bigr), \qquad (a, u) = e^{-1}(q) .$$
--
--   So the gradient of the branch cost in its first endpoint is minus the inverse-branch velocity: the first-variation formula of the paper's Section 2.1, at every point of the branch. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_gradient`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/BranchInitialGeometry.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/BranchInitialGeometry.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_gradient)

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
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem branch_initial_gradient (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {q : Model n × Model n} (hq : q ∈ e.target) (w : Model n) :
    fderiv ℝ (fun a => branchAction x e (a,q.2)) q.1 w = -metric x q.1 (e.symm q).2 w := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

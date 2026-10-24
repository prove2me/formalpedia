-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_branch_initial_radial
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_radial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:47:41.006984+00:00
-- url     : https://prove2.me/theorems/a1f89db1-654f-4b95-969e-593aa9bd4d9d
-- title:
--   Radial identity for the branch Hessian, A(w)(w, ·) = ⟨w, ·⟩ (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statement `OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_gradient` of this split: $e$ is a smooth local inverse of the exponential pair map in charts, the branch cost $\hat c$ (`branchAction x e`) is half the squared norm of the inverse-branch velocity, and $g$ is the metric read in the chart at $x$ (`metric x`), with Christoffel map $\Gamma$. For a function $f$ on $\mathbb R^n$ and vectors $a, \nu$, `actionForm g f a ν` is the bilinear form
--   $$(\xi, \eta) \mapsto D^2 f(a)(\xi, \eta) + g_a\bigl(\nu, \Gamma_a(\xi, \eta)\bigr),$$
--   the coordinate covariant Hessian of $f$ at $a$ when $df_a = -g_a(\nu, \cdot)$.
--
--   **Statement.** Let $e$ agree with `pairExpCoordinates x y`, with source inside `pairExpDomain x y` and a $C^\infty$ inverse on its target. For every $q = (a, b)$ in the target of $e$, with $(a, u) = e^{-1}(q)$, and every $w \in \mathbb R^n$, the form for $f = \hat c(\cdot, b)$ and $\nu = u$ satisfies
--   $$\texttt{actionForm}\ g\ f\ a\ u\ (w, u) = g_a(w, u) .$$
--
--   This is the paper's identity (2.5), $A_x(w)(w, \cdot) = \langle w, \cdot\rangle_x$, at every point of a smooth branch: the branch Hessian acts as the metric in the radial direction. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_radial`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/BranchInitialGeometry.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/BranchInitialGeometry.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_radial)

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

 theorem branch_initial_radial (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {q : Model n × Model n} (hq : q ∈ e.target) (w : Model n) :
    actionForm (metric x) (fun a => branchAction x e (a,q.2)) q.1 (e.symm q).2
      w (e.symm q).2 = metric x q.1 w (e.symm q).2 := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

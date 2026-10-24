-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_actionHessian_eq_branch
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.actionHessian_eq_branch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:46:26.91209+00:00
-- url     : https://prove2.me/theorems/77f6f7e8-4610-40bd-a17b-9b2bb7a8fdb8
-- title:
--   On the injectivity domain, the cost Hessian equals the branch Hessian (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statement `OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.exists_of_nonconjugate` of this split ($M$ compact Riemannian, `pairExpCoordinates x y` the exponential pair map in charts). The cost is $c(x, y) = d(x, y)^2/2$ (`cost`), and the injectivity domain `injectivityDomain x` is the set of $v \in T_xM$ whose geodesic $\exp_x(tv)$ still minimizes a little beyond $t = 1$: $d(x, \exp_x(av)) = a\|v\|$ for some $a > 1$. Write $a = \varphi_x(x)$, $b = \varphi_y(\exp_x v)$ for chart coordinates, $g$ for the metric read in the chart at $x$ (`metric x`), and $\Gamma$ for its Christoffel map.
--   - `actionHessian x v` is the coordinate form of the covariant Hessian at $x$ of $c(\cdot, \exp_x v)$, pulled back to $T_xM$: $\xi \mapsto D^2 f(a)(\xi, \xi) + g_a(v, \Gamma_a(\xi, \xi))$ with $f$ = `initialCost x (exp x v)`, the cost read in the chart at $x$ (`actionForm`).
--   - For a local inverse $e$ of the pair map, `branchHessianDiag x y e v ξ` is the same expression with the branch cost $\hat c$ (`branchAction x e`, half the squared norm of the inverse-branch velocity) in place of the cost, second endpoint fixed at $b$.
--
--   **Statement.** Let $e$ be an open partial homeomorphism of $\mathbb R^n \times \mathbb R^n$ that agrees with `pairExpCoordinates x y`, has source inside `pairExpDomain x y` and a $C^\infty$ inverse on its target. If $v \in$ `injectivityDomain x` and the tangent-bundle coordinates of $(x, v)$ lie in the source of $e$, then for every $\xi \in T_xM$
--   $$\texttt{actionHessian}\ x\ v\ \xi\ \xi = \texttt{branchHessianDiag}\ x\ y\ e\ v\ \xi .$$
--
--   This is the remark of the paper's Section 2.1 that for $w \in I(x)$ the branch cost agrees locally with $c$, so that the branch Hessian $A_x(w)$ of its equation (2.4) is the Hessian of the cost. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.actionHessian_eq_branch`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/BranchHessian.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/BranchHessian.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.actionHessian_eq_branch)

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
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem actionHessian_eq_branch (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (hev : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source)
    (ξ : TangentSpace (model n) x) : actionHessian x v ξ ξ = branchHessianDiag x y e v ξ := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

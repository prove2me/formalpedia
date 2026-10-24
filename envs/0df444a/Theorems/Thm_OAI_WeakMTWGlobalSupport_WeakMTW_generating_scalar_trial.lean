-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_generating_scalar_trial
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.generating_scalar_trial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:49:02.830302+00:00
-- url     : https://prove2.me/theorems/6437d491-a693-475b-a430-45a11011bd16
-- title:
--   Trial bound for the action Hessian by the generating Hessian (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statements `OAI.WeakMTWGlobalSupport.WeakMTW.exists_generating_neighborhood` and `OAI.WeakMTWGlobalSupport.WeakMTW.generatingHessian_focal` of this split. In addition:
--   - `injectivityDomain x` is $I(x)$, the velocities $v$ with $d(x, \exp_x(av)) = a\|v\|$ for some $a > 1$.
--   - `tangentChartLinear x` is the derivative at $x$ of the chart at $x$, identifying $T_xM$ with $\mathbb R^n$. Write $\hat\xi$ for the image of $\xi$.
--   - The **action Hessian** `actionHessian x v` is the bilinear form on $T_xM$ obtained from the coordinate Hessian of the initial cost $a \mapsto c(\text{chart}_x^{-1}(a), \exp_x v)$ at $x$, corrected by the Christoffel term: $\mathrm{actionForm}(v, w) = D^2 f(v, w) + \Gamma^\flat(v, w)(\hat v)$, with $\Gamma^\flat$ = `lowerChristoffel` of the derivative of the chart metric. For $v \in I(x)$, where the gradient of the initial cost is $-v$ (the statement `OAI.WeakMTWGlobalSupport.WeakMTW.initialCost_geometry` of this split), this is the covariant Hessian of $c(\cdot, \exp_x v)$ at $x$.
--
--   **Statement.** Let $0 < \varepsilon < 1$, let $v \in I(x)$, and suppose `GeneratingChartAction x y ε` holds at the chart state of $(x, v)$. Write $H$ for `generatingHessian x y ε` at that state, $A = ((\hat\xi, 0), 0)$ and $K = ((0, \kappa), 0)$. Then for every $\xi \in T_xM$, $\kappa \in \mathbb R^n$ and $\alpha \in \mathbb R$,
--   $$\mathrm{actionHessian}_x(v)(\xi, \xi) \le \bigl(H(A, A) + \Gamma^\flat(\hat\xi, \hat\xi)(\hat v)\bigr) + 2\alpha\, H(A, K) + \alpha^2 H(K, K).$$
--
--   The action Hessian is bounded by a quadratic polynomial in $\alpha$, the Hessian of the generating action along the trial direction $A + \alpha K$. This is the Lean counterpart of testing Lemma 2.2 of the paper on $E_a + \lambda J_a$, which gives the quadratic bound (3.1) in the proof of Proposition 3.1. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.generating_scalar_trial`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/GeneratingQuadratic.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and from the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/GeneratingQuadratic.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.generating_scalar_trial)

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

 theorem generating_scalar_trial (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (hq : GeneratingChartAction x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)))
    (ξ : TangentSpace (model n) x) (κ : Model n) (α : ℝ) :
    actionHessian x v ξ ξ ≤
      (generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((tangentChartLinear x ξ,0),0) ((tangentChartLinear x ξ,0),0) +
      lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
        (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x v)) +
      2*α*generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((tangentChartLinear x ξ,0),0) ((0,κ),0) +
      α^2*generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((0,κ),0) ((0,κ),0) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
